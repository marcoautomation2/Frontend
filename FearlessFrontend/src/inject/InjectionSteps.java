package inject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.B;
import core.LiteralDeclarations;
import core.MName;
import core.RC;
import core.TName;
import core.TSpan;
import inference.E;
import inference.Gamma;
import inference.IT;
import inference.IT.RCC;
import inference.M;
import utils.Bug;
import utils.OneOr;
import utils.Push;
import utils.Range;
import utils.Streams;

/**
Inference fix-point core loop relies on identity for E.
Core loop relies on `oe == e` to detect stabilization in O(1) and avoid a deep
`equals(e)` walk each iteration:
`if (oe == e && !g.changed(s)){ e.sign(g); return e; }`
Any rewrite of terms containing Es MUST return the original
instance (==) if no structural change is performed.

Exact identity-sensitive set
(must preserve == on no-op updates, including inside Optional/List/Map containers):
- inference.E.X
- inference.E.Type
- inference.E.Call
- inference.E.Literal
- inference.M
- inference.M.Impl
Any other form of allocation prevention is just premature optimization
and should be simplified away.
Only preserve identity (==) for E/M (and their deciding containers like List<E>/List<M>/Optional<M.Impl>).
For IT/Sig/TName (and List<IT>/List<Optional<IT>> etc.) NEVER do "same -> return old": allocate freely.

Non-identity-sensitive (allocation/equal ok): types (IT), signatures (Sig), names (TName),
and other data that cannot contain E.

Offensive style: Optional.get() is intentional where invariants guarantee presence;
absence indicates a bug and should crash.
*/

public record InjectionSteps(Methods meths, int cap, boolean late){
  public static List<core.E.Literal> steps(Methods meths, List<E.Literal> tops){
    var s= new InjectionSteps(meths, deepest(meths), false);
    assert tops.stream().allMatch(l -> l.thisName().equals("this"));
    //No! at this point they have been (correctly) divided in layers assert tops.stream().sorted().toList().equals(tops);
    return tops.stream()
      .map(l -> s.stepDec(meths.cache().get(l.name()), l)).toList();
  }
  private static int deepest(Methods meths){
    var ds= Stream.concat(meths.cache().values().stream(), meths.other().dom().stream().map(meths::from));
    return ds.flatMapToInt(InjectionSteps::depths).max().orElse(1);
  }
  private static IntStream depths(core.E.Literal d){
    var cs= d.cs().stream().mapToInt(c -> TypeRename.tcToITC(c).depth());
    var ms= d.ms().stream().flatMap(m -> Push.of(m.sig().ts(), m.sig().ret()).stream()).mapToInt(t -> TypeRename.tToIT(t).depth());
    return IntStream.concat(cs, ms);
  }
  private static int size(IT t){ return t instanceof IT.RCC rcc ? size(rcc.c()) : 1; }
  private static int size(IT.C c){ return 1+c.ts().stream().mapToInt(InjectionSteps::size).sum(); }
  private static int size(M m){
    var ts= Push.of(m.sig().ts(), m.sig().ret()).stream().mapToInt(t -> t.map(InjectionSteps::size).orElse(1)).sum();
    return ts+m.impl().map(i -> size(i.e())).orElse(0);
  }
  private static int size(E e){ return size(e.t())+switch (e){
    case E.X _ -> 0;
    case E.Type t -> size(t.type());
    case E.Call c -> size(c.e())+c.targs().stream().mapToInt(InjectionSteps::size).sum()+c.es().stream().mapToInt(InjectionSteps::size).sum();
    case E.Literal l -> l.cs().stream().mapToInt(InjectionSteps::size).sum()+l.ms().stream().mapToInt(InjectionSteps::size).sum();
  };}
  private core.E.Literal stepDec(core.E.Literal di, E.Literal li){ return di.withMs(Streams.zip(di.ms(), li.ms()).map((mCore, m) -> stepDecM(di, mCore, m)).toList()); }
  private core.M stepDecM(core.E.Literal di, core.M mCore, M m){
    if (m.impl().isEmpty()){ return mCore; }//assert same type as m lifted to core
    var e= m.impl().get().e();
    var span= di.name().approxSpan();
    var xs= m.xs();
    var thisRc= LiteralDeclarations.has(di.cs(), LiteralDeclarations.captureFree) ? RC.imm : mCore.sig().rc();
    var thisType= new IT.RCC(Optional.of(thisRc), new IT.C(di.name(), MSigL.toXs(span, B.xs(di.bs()))), span);//no preferred on self names
    var ei= meet(e, TypeRename.tToIT(mCore.sig().ret()));
    var g= Gamma.of(xs, TypeRename.tToIT(mCore.sig().ts()), di.thisName(), thisType);
    var bs= Push.of(di.bs(), m.sig().bs().get());
    var limit= cap*size(ei);
    ei = new InjectionSteps(meths, limit, false).nextStar(bs, g, ei);
    g.tableGrew();
    ei = new InjectionSteps(meths, limit, true).nextStar(bs, g, ei);
    return new core.M(mCore.sig(), xs, m.names(), Optional.of(new ToCore(bs, meths).of(ei, e)));
  }
  E meet(E e, IT t){
    if (e instanceof E.Type tt){ return meetT(tt, t); }
    var typedLit= e instanceof E.Literal l && l.t().isTV();
    if (typedLit){ return e; }
    e = prototypeAscribeRootReceiver(e, t, Optional.empty());
    return e.withT(meet(e.t(), t));
  }
  private IT _below(RCC sub, RCC sup){
    var d= meths._from(sub.c().name());
    if (d == null || d.cs().stream().noneMatch(c -> c.name().equals(sup.c().name()))){ return null; }
    var xs= B.xs(d.bs());
    var generic= new IT.RCC(Optional.empty(), new IT.C(sub.c().name(), MSigL.toXs(sub.span(), xs)), sub.span());
    var res= sub.withRCTs(meetRcNoH(sub.rc(), sup.rc()), meet(sub.c().ts(), refine(xs, generic, sup)));
    return res.isTV() || !sup.isTV() ? res : sup;
  }
  IT meet(IT t1, IT t2){
    if (t2.undecided()){ return t1 instanceof IT.U ? t2 : t1; }
    if (t1.undecided()){ return t2; }
    if (t1.equals(t2)){ return t1; }
    if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){
      if (!x1.c().name().equals(x2.c().name())){
        var s= _below(x1, x2);
        if (s == null){ s = _below(x2, x1); }
        return s == null ? x1 : s;
      }
      var rc= meetRcNoH(x1.rc(), x2.rc());
      return x1.withRCTs(rc, meet(x1.c().ts(), x2.c().ts()));
    }
    if (!(t1 instanceof IT.RCX x1 && t2 instanceof IT.RCX(var rc2, var x2)) || !x1.x().equals(x2)){ return t1; }
    return x1.withRC(meetRcNoH(Optional.of(x1.rc()), Optional.of(rc2)).get());
  }
  static Optional<RC> meetRcNoH(Optional<RC> a, Optional<RC> b){
    if (a.isEmpty()){ return b; }
    if (b.isEmpty()){ return a; }
    var x= noH(a.get());
    var y= noH(b.get());
    return Optional.of(x.compareTo(y) < 0 ? x : y);// returning Optional.empty(); could make it go in loop
  }
  static RC noH(RC a){ return a == RC.readH ? RC.read : a == RC.mutH ? RC.mut : a; }
  IT join(IT t1, IT t2){
    if (t2 instanceof IT.U){ return t1; }
    if (t1 instanceof IT.U){ return t2; }
    if (t1.equals(t2)){ return t1; }
    var cands= Push.of(candidates(t1), candidates(t2));
    for (var top : cands){ var res= _aboveAll(top, cands); if (res != null){ return res; } }
    var common= _commonSupertype(cands);
    return common == null ? new IT.Amb(cands) : _aboveAll(common, cands);
  }
  private IT _commonSupertype(List<IT> cands){
    var minimal= meths.commonSuperHeads(cands);
    if (minimal.size() != 1){ return null; }
    return adaptedSuperTs((IT.RCC)cands.getFirst(), minimal.getFirst()).getFirst();
  }
  private static List<IT> candidates(IT t){ return t instanceof IT.Amb(var cs) ? cs : List.of(t); }
  private IT _aboveAll(IT top, List<IT> cands){
    IT res= top;
    for (var c : cands){
      var up= _liftTo(c, top);
      if (up == null){ return null; }
      res = _sameShapeJoin(res, up);
      if (res == null){ return null; }
    }
    return res;
  }
  private IT _liftTo(IT c, IT top){
    if (c instanceof IT.RCC rc && top instanceof IT.RCC rt){
      if (rc.c().name().equals(rt.c().name())){ return c; }
      var up= adaptedSuperTs(rc, rt.c().name());
      return up.size() != 1 ? null : up.getFirst();
    }
    var sameX= xName(c).isPresent() && xName(c).equals(xName(top));
    return sameX ? c : null;
  }
  private IT _sameShapeJoin(IT a, IT b){
    if (a instanceof IT.RCC x1 && b instanceof IT.RCC x2){
      var differ= Streams.zip(x1.c().ts(), x2.c().ts()).anyMatch((t1,t2) -> t1.isTV() && t2.isTV() && !t1.equals(t2));
      if (differ){ return null; }
      return x1.withRCTs(joinRcNoH(x1.rc(), x2.rc()), meet(x1.c().ts(), x2.c().ts()));
    }
    if (a instanceof IT.RCX x1 && b instanceof IT.RCX x2){ return x1.withRC(joinRcNoH(Optional.of(x1.rc()), Optional.of(x2.rc())).get()); }
    return meet(a, b);
  }
  static Optional<RC> joinRcNoH(Optional<RC> a, Optional<RC> b){
    if (a.isEmpty()){ return b; }
    if (b.isEmpty()){ return a; }
    var x= noH(a.get());
    var y= noH(b.get());
    return Optional.of(x == y || y == RC.iso ? x : x == RC.iso ? y : RC.read);
  }
  List<IT> join(List<IT> t1, List<IT> t2){ return Streams.zip(t1, t2).map(this::join).toList(); }
  List<IT> meet(List<IT> t1, List<IT> t2){ return Streams.zip(t1, t2).map(this::meet).toList(); }
  E nextStar(List<B> bs, Gamma g, E e){
    var start= e;
    if (e.done(g)){ return e; }
    while (true){
      var s= g.snapshot();
      var oe= next(bs, g, e);
      assert oe == e || !oe.equals(e) : "Allocated equal E:"+e.getClass()+"\n"+e;
      var stable= oe == e && !g.changed(s);
      if (stable){
        e.sign(g);
        assert e == start || !e.equals(start);
        return e;
      }
      //if (oe.equals(e) && !g.changed(s)){ e.sign(g); return e; }//this line is useful for debugging when == gets buggy
      var forever= oe.t().depth() > cap;
      if (forever){ throw meths.p().err().typeGrowsForever(oe); }
      e = oe;
    }
  }
  private List<E> nextStar(List<B> bs, Gamma g, List<E> es){
    return norm(es, es.stream().map(ei -> nextStar(bs, g, ei)).toList());
  }
  private List<E> meetWithTargs(List<E> es, MSigL m, List<IT> targs){
    var res= norm(es, Streams.zip(es, m.ps0()).map((e,p) -> meet(e, m.inst(p, targs))).toList());
    assert notBackToOrigin(es, res);
    return res;
  }
  private boolean notBackToOrigin(List<E> originEs, List<E> res){
    //complex but invaluable: if it fails it means we are going 'back and forth'
    //and this could cause loops.
    return Streams.zip(res, originEs).allMatch((r,o) -> r == o || !r.equals(o));
  }
  E next(List<B> bs, Gamma g, E e){
    return switch (e){
      case E.X x -> nextX(g, x);
      case E.Literal l -> nextL(bs, g, l);
      case E.Call c -> nextC(bs, g, c);
      case E.Type c -> nextT(c);
    };
  }
  private IT preferred(IT.RCC type){
    var c= OneOr.opt("Repeated WidenTo supertype", adaptedSuperTs(type, LiteralDeclarations.widen).stream());
    if (c.isEmpty() || !(OneOr.of("WidenTo has one type argument", c.get().c().ts().stream()) instanceof IT.RCC(_, var widC, _))){ return type; }
    return new IT.RCC(type.rc(), widC, type.span());
  }
  private RC overloadNorm(Optional<RC> rc){ return rc.map(r -> r == RC.iso ? RC.imm : noH(r)).orElse(RC.imm); }
  private Optional<core.M> oneFromGuessRC(List<core.M> ms, RC rc){
    return Stream.of(rc, RC.read, RC.imm, RC.mut).flatMap(r -> OneOr.opt("Not well formed ms", ms.stream().filter(m -> m.sig().rc() == r)).stream()).findFirst();
  }
  private Optional<MSigL> methodHeader(IT.RCC rcc, MName name, Optional<RC> favorite, RC guess){
    var d= meths._from(rcc.c().name());
    if (d == null){ return Optional.empty(); }//case {..}.foo
    var ms= d.ms().stream().filter(m -> m.sig().m().equals(name));
    var om= favorite
      .map(rc -> OneOr.opt("Ambiguous method header for explicit RC", ms.filter(mi -> mi.sig().rc() == rc)))
      .orElseGet(() -> oneFromGuessRC(ms.toList(), guess));
    return om.map(mm -> methodHeaderInstance(rcc, d, mm));
  }
  private MSigL methodHeaderInstance(IT.RCC rcc, core.E.Literal d, core.M m){
    var clsXs= B.xs(d.bs());
    assert Set.copyOf(clsXs).size() == clsXs.size();
    var methXs= B.xs(m.sig().bs());
    assert Set.copyOf(methXs).size() == methXs.size();
    assert Collections.disjoint(clsXs, methXs);
    var clsArgs= rcc.c().ts();
    assert clsArgs.size() == clsXs.size();
    var xs= Push.of(clsXs, methXs);//TODO: could avoid materializing the two lists
    var ps0= TypeRename.tToIT(m.sig().ts());
    var ret0= TypeRename.tToIT(m.sig().ret());
    return new MSigL(m.sig().rc(), xs, d.bs(), clsArgs, m.sig().bs(), ps0, ret0);
  }
  Optional<MSigL> methodHeader(IT.RCC rcc, MName name, Optional<RC> favorite){
    return methodHeader(rcc, name, favorite, overloadNorm(rcc.rc()));
  }
  static List<IT> qMarks(int n){ return Stream.<IT>generate(() -> IT.U.Instance).limit(n).toList(); }
  private List<IT> qMarks(int n, IT t, int tot){ return IntStream.range(0, tot).<IT>mapToObj(i -> i == n ? t : IT.U.Instance).toList(); }
  private E nextX(Gamma g, E.X x){
    var t1Base= g.get(x.name());
    var notIn= g.notFunnelledInto(x.name());
    if (notIn.isPresent()){ throw meths.p().err().captureNotFunnelled(x, t1Base, notIn.get()); }
    var t1= g.getWithRC(x.name());
    var t2= x.t();
    if (t1.equals(t2)){ return x; }
    if (!t2.undecided()){ updateG(g, x.name(), t1Base, t2); }
    return x.withT(meet(t1, t2));
  }
  private void updateG(Gamma g, String x, IT t1, IT t2){
    if (t1.undecided()){ g.update(x, t2 instanceof IT.RCC(_, var c, var span) ? new RCC(Optional.empty(), c, span) : t2); return; }
    if (t1 instanceof IT.RCC a && t2 instanceof IT.RCC b && a.c().name().equals(b.c().name())){ g.update(x, meet(t1, t2)); }
  }
  private E nextT(E.Type t){
    if (!t.t().undecided()){ return t; }
    return t.withT(preferred(t.type()));
  }
  private E meetT(E.Type tt, IT t){
    if (!emptyLiteral(tt) || !(meet(tt.t(), t) instanceof IT.RCC met) || !met.isTV()){ return nextT(tt); }
    var r= selfArgument(met);
    if (r.equals(tt.type())){ return nextT(tt); }
    var res= new E.Type(r, preferred(r), tt.src(), tt.g().clear());
    notForeignPrivate(res, r);
    return res;
  }
  private E nextC(List<B> bs, Gamma g, E.Call c){
    var e= nextStar(bs, g, c.e());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e, nextStar(bs, g, c.es())); }
    var guess= overloadNorm(rcc.rc().map(rc -> rc == RC.iso ? c.t().explicitRC().orElse(rc) : rc));
    var direct= methodHeader(rcc, c.name(), c.rc(), guess);
    var om= direct.isPresent() ? direct : methodHeader((IT.RCC)deFresh(g, rcc), c.name(), c.rc(), guess);
    if (om.isEmpty()){ return c.withEEs(e, nextStar(bs, g, c.es())); }
    var m= om.get();
    assert m.ps0().size() == c.es().size();
    var all= decidedThen(g, c, m);
    assert all.size() == m.nCls()+m.bsArity();
    var clsTs= all.subList(0, m.nCls());
    var targs= all.subList(m.nCls(), all.size());
    if (direct.isPresent()){ e = meet(e, rcc.withTs(clsTs)); }
    m = m.withClsArgs(clsTs);
    var it= meet(c.t(), m.ret(targs));
    var es1= nextStar(bs, g, meetWithTargs(c.es(), m, targs));
    var noChange= e == c.e() && es1 == c.es() && targs.equals(c.targs()) && it.equals(c.t());
    if (noChange){ return c; }
    return c.withMore(e, c.rc().orElse(m.rc()), targs, es1, it);
  }
  private static IT deFresh(Gamma g, IT t){
    if (!(t instanceof IT.RCC rcc)){ return t; }
    var o= g._owner(rcc.c().name());
    var head= o != null && o.infName() && o.t() instanceof IT.RCC h && !h.c().name().equals(o.name()) ? h.c() : rcc.c();
    return new IT.RCC(rcc.rc(), head, rcc.span()).withTs(head.ts().stream().map(ti -> deFresh(g, ti)).toList());
  }
  private List<IT> decidedThen(Gamma g, E.Call c, MSigL m){
    var given= Push.of(m.clsArgs(), writtenTargs(c) ? MSigL.fixTargs(c.targs(), m.bsArity()) : qMarks(m.bsArity()));
    var args= Streams.zip(m.ps0(), c.es()).map((p,e) -> new Con(p, e.t(), true, !emptyLiteral(e))).toList();
    return decide(g, Push.of(m.clsBs(), m.methBs()), given, Push.of(new Con(m.ret0(), c.t(), false, true), args));
  }
  private record Con(IT declared, IT actual, boolean in, boolean eq){}
  private List<IT> decide(Gamma g, List<B> bs, List<IT> given, List<Con> cons){
    var xs= B.xs(bs);
    Function<Con, List<IT>> ref= c -> refine(xs, c.declared(), c.actual());
    var shape= cons.stream().filter(c -> c.eq() && c.declared() instanceof IT.RCC).map(ref).reduce(given, this::meet);
    var lifted= join(shape, cons.stream().filter(c -> c.in() && !(c.declared() instanceof IT.RCC)).map(ref).reduce(qMarks(xs.size()), this::join));
    var all= cons.stream().filter(c -> c.declared() instanceof IT.RCC ? !c.eq() : !c.in()).map(ref).reduce(lifted, this::meet);
    var res= Stream.of(given, shape, all).reduce((p,q) -> Streams.zip(p, q).map((a,b) -> a.isTV() ? a : b).toList()).get();
    return normToBounds(bs, res.stream().map(t -> deFresh(g, t)).toList());
  }
  private static boolean emptyLiteral(E e){ return e instanceof E.Type tt ? tt.src().inner instanceof fearlessFullGrammar.E.Literal : e instanceof E.Literal l && l.infName() && l.ms().isEmpty(); }
  static boolean writtenTargs(E.Call c){ return c.src().inner instanceof fearlessFullGrammar.E.Call sc && sc.targs().isPresent(); }
  private Optional<IT.RCC> preciseSelf(E.Literal l){
    var selfUnknown= l.infName() && l.rc().isEmpty();
    if (selfUnknown){ return Optional.empty(); }
    var span= l.name().approxSpan();
    return Optional.of(new IT.RCC(l.rc(), new IT.C(l.name(), MSigL.toXs(span, B.xs(l.bs()))), span));
  }
  private E nextL(List<B> bs, Gamma g, E.Literal l){
    var infHead= l.infHead();//infHead is set in l.withCsMs and l.withMsT
    // to mean the HEAD is inferred as IT.RCC and has already been used to expand methods
    var selfPrecise= preciseSelf(l);
    if (!infHead){
      l = l.infName() && l.cs().size() == 1 ? l.withT(new IT.RCC(l.rc(), l.cs().getFirst(), l.name().approxSpan())) : selfPrecise.map(l::withT).orElse(l);
      if (!(l.t() instanceof IT.RCC(_, var c, _))){ return l; }//!infHead after passing this test means right now we can expand methods
      var anon= l.infName() && !c.name().equals(l.name());
      var o= anon ? g._owner(c.name()) : null;
      if (o != null && o.infName()){ throw meths.p().err().implementsAnonymousType(l, o); }
      l = anon ? meths.expandLiteral(l, c, bs) : meths.expandDeclaration(l, true);
    }
    if (!(l.t() instanceof IT.RCC rcc)){ return l; }
    var solved= new ArrayList<M>(l.ms().size());
    for (var mi : l.ms()){
      assert mi.impl().isEmpty() || selfPrecise.isEmpty() || rcc.isTV();
      solved.add(mi.impl().isEmpty() ? mi : nextMStarOp(bs, g, l, selfPrecise, rcc, mi));
    }
    var d= meths._from(rcc.c().name());
    var ts= d == null ? rcc.c().ts().stream().map(t -> deFresh(g, t)).toList() : decide(g, d.bs(), rcc.c().ts(), solved.stream().flatMap(m -> constraints(rcc, m)).toList());
    var t= rcc.withTs(ts);
    var ms= norm(l.ms(), Streams.zip(l.ms(), solved).map((mi, m) -> instantiate(t, mi, m)).toList());
    var noChange= ms == l.ms() && ts.equals(rcc.c().ts());
    if (noChange){ return commitToTable(g, bs, l, rcc); }
    return commitToTable(g, bs, l.withMsT(ms, t), t);
  }
  private E commitToTable(Gamma g, List<B> bs, E.Literal l, IT.RCC rcc){
    var name= l.name();
    var notReady= !rcc.isTV() || hasU(l.ms()) || meths.cache().containsKey(name);
    if (notReady){ return l; }
    var freeNames= Streams.of(new FreeXs(g).ftvMs(l.ms()), new FreeXs(g).ftvCs(l.cs()), rcc.ftv());
    var localBs= freeNames.distinct().map(x -> B.get(bs, x)).toList();
    var newName= name.withArity(localBs.size());
    var ms= fixArity(l.ms(), name, newName);
    var orc= l.rc().or(rcc::rc).map(InjectionSteps::noH);
    assert l.infName();
    assert l.bs().isEmpty();
    var noMeth= l.ms().stream().allMatch(m -> m.impl().isEmpty());
    var selfInferred= rcc.c().name().equals(l.name());
    if (noMeth && !selfInferred && meths._from(rcc.c().name()) != null){ return literalAsType(l, rcc); }
    notForeignPrivate(l, rcc);
    var cs= ToCore.distinctTypes(localBs, selfInferred ? meths.implied(rcc.c()) : Push.of(rcc.c(), meths.implied(rcc.c())));
    assert l.infHead();
    l = new E.Literal(orc, newName, localBs, cs, l.thisName(), ms, rcc, l.src(), l.infName(), l.infHead(), l.g());
    meths.checkMagicSupertypes(l, cs);
    if (selfInferred){ l = l.withT(preciseSelf(l).get()); }
    assert !meths.cache().containsKey(name);
    meths.register(l);
    return l;
  }
  private E.Type literalAsType(E.Literal l, IT.RCC rcc){
    if (!l.thisName().equals("_")){ throw meths.p().err().selfNameDeadCode(l); }
    var written= new IT.RCC(l.rc().or(rcc::rc).map(InjectionSteps::noH), rcc.c(), rcc.span());
    notForeignPrivate(l, written);
    return new E.Type(written, preferred(written), l.src(), l.g());
  }
  private void notForeignPrivate(E owner, IT.RCC t){
    var head= t.c().name();
    var foreignPrivate= !head.isPublic() && !head.pkgName().equals(meths.p().name());
    if (foreignPrivate){ throw meths.p().err().extendedForeign(owner, head, "private"); }
  }
  private IT.RCC selfArgument(IT.RCC t){
    var c= t.c();
    var instantiable= meths._from(c.name()).ms().stream().noneMatch(m -> m.sig().abs() && m.sig().rc() != RC.mut);
    if (instantiable){ return t; }
    var selves= c.ts().stream().flatMap(ti -> ti instanceof IT.RCC r && meths.implied(r.c()).contains(c) ? Stream.of(r.c()) : Stream.of()).distinct().toList();
    return selves.size() == 1 ? new IT.RCC(t.rc(), selves.getFirst(), t.span()) : t;
  }
  private List<M> fixArity(List<M> ms, TName name, TName newName){
    if (name.equals(newName)){ return ms; }
    return norm(ms, ms.stream().map(mi -> fixArity(mi, name, newName)).toList());
  }
  private M fixArity(M m, TName name, TName newName){
    var s= m.sig();
    if (!s.origin().get().equals(name)){ return m; }
    return m.withSig(s.withOrigin(newName));
  }
  private static boolean hasU(List<M> ms){
    return !ms.stream()
      .allMatch(m -> m.sig().ret().get().isTV() && m.sig().ts().stream().allMatch(t -> t.get().isTV()));
  }
  private List<Optional<IT>> updateArgs(M m, Gamma g){
    return Streams.zip(m.xs(), m.sig().ts()).map((x,oi) -> x.equals("_") || !late ? oi : Optional.of(meet(oi.get(), g.get(x)))).toList();
  }
  M nextMStarOp(List<B> bs, Gamma g, E.Literal l, Optional<IT.RCC> selfPrecise, IT.RCC rcc, M m){
    assert m.impl().isPresent();
    var litBs= l.infName() ? bs : l.bs();
    g.newScope(m.sig().rc().get(), litBs, l);
    g.declare(l.thisName(), selfPrecise.<IT>map(s -> new IT.RCC(captureFree(l) ? Optional.of(RC.imm) : m.sig().rc(), s.c(), s.span())).orElse(IT.U.Instance));
    assert m.sig().m().get().arity() == m.xs().size();
    Streams.zip(m.xs(), m.sig().ts()).forEach((x,t) -> g.declare(x, t.get()));
    var e= nextStar(Push.of(litBs, m.sig().bs().get()), g, meet(m.impl().get().e(), m.sig().ret().get()));
    var args= updateArgs(m, g);
    g.popScope();
  /*The meet below narrows a method's return type to the type of its body, so a literal only ever
  gets more precise than what the use site asked for. What keeps that from destroying an invariant
  instantiation is that a decided type argument is never re-decided: meetWithTargs in nextC and the meet in
  nextMStarOp push what is already known down before a body is inferred, and keepDecided then only
  fills the type arguments still unknown. See the five tests named in TypeSystemTest, next to
  blockLetInfersItsTypeFromTheLambdaBody, for what base needs the meet itself for.*/
    var ret= meet(m.sig().ret().get(), e.t());
    return new M(m.sig().withTsT(args, ret), m.xs(), m.names(), Optional.of(new M.Impl(m.impl().get().m(), e)));
  }
  private Stream<Con> constraints(IT.RCC rcc, M m){
    var sig= m.sig();
    var oh= methodHeader(rcc, sig.m().get(), sig.rc());
    if (oh.isEmpty()){ return Stream.of(); }
    var methXs= B.xs(sig.bs().get());
    var ps= Streams.zip(oh.get().ps0(), sig.ts()).map((p,a) -> new Con(p, dropMethBs(a.get(), methXs), false, true));
    return Stream.concat(ps, Stream.of(new Con(oh.get().ret0(), dropMethBs(sig.ret().get(), methXs), true, true)));
  }
  private static boolean captureFree(E.Literal l){ return l.cs().stream().anyMatch(c -> c.name().equals(LiteralDeclarations.captureFree)); }
  private M instantiate(IT.RCC t, M orig, M m){
    var sig= m.sig();
    var xs= MSigL.toXs(sig.span(), B.xs(sig.bs().get()));
    var norm= methodHeader(t, sig.m().get(), sig.rc()).map(h -> sig.withTsT(h.ps0().stream().map(p -> Optional.of(h.inst(p, xs))).toList(), h.inst(h.ret0(), xs))).orElse(sig);
    if (orig.impl().isEmpty()){ return orig.withSig(norm); }
    var impl= orig.impl().get().withE(m.impl().get().e());
    var noChange= norm.equals(orig.sig()) && impl == orig.impl().get();
    return noChange ? orig : new M(norm, orig.xs(), orig.names(), Optional.of(impl));
  }
  List<IT> dropMethBs(List<IT> ts, List<String> methBs){
    if (methBs.isEmpty()){ return ts; }
    return ts.stream().map(t -> dropMethBs(t, methBs)).toList();
  }
  IT dropMethBs(IT t, List<String> methBs){
    if (t instanceof IT.RCC rcc){ return rcc.withTs(dropMethBs(rcc.c().ts(), methBs)); }
    return xName(t).filter(methBs::contains).isPresent() ? IT.U.Instance : t;
  }
  List<IT> refine(List<String> xs, IT t, IT t1){
    if (t1.undecided()){ return qMarks(xs.size()); }
    return switch (t){
      case IT.X x -> qMarks(xs.indexOf(x.name()), t1, xs.size());
      case IT.RCX(_, var x) -> refine(xs, x, stripRCAlsoThisSide(t1));
      case IT.ReadImmX(var x) -> refine(xs, x, t1 instanceof IT.ReadImmX(var x1) ? x1 : t1);
      case IT.RCC rcc -> propagateXs(xs, rcc, t1);
      case IT.U _, IT.Amb _ -> throw Bug.unreachable(); //stripRCAlsoThisSide is needed to distinguish
    };//xs=[EE], t= imm EE, t1=imm ET -> [ET] | xs=[EE], t= EE, t1=imm ET ->[imm ET]
  }
  //xs=[EE], t= EE, t1=imm ET ->[imm ET]
  //xs=[EE], t= imm EE, t1=imm ET -> [ET]
  //xs=[EE], t= imm EE, t1=read Foo[Bar] -> [?? Foo[Bar]]
  //xs=[EE], t= imm EE, t1=ET -> [ET]//but only if ET only bound is ET:imm?
  static IT stripRCAlsoThisSide(IT t){ return switch (t){
    case IT.X x -> x;//IT.U.Instance;
    case IT.RCX(_, var x) -> x;
    case IT.ReadImmX(var x) -> x;
    case IT.RCC(_, var c, var span) -> new IT.RCC(Optional.empty(), c, span);
    case IT.U _, IT.Amb _ -> throw Bug.unreachable();
  };}
  private List<IT.RCC> adaptedSuperTs(IT.RCC src, TName target){
    return meths.implied(src.c()).stream().filter(c -> c.name().equals(target)).map(c -> new IT.RCC(src.rc(), c, src.span())).toList();
  }
  List<IT> propagateXs(List<String> xs, IT.RCC r, IT t1){
    if (!(t1 instanceof IT.RCC cc)){ return qMarks(xs.size()); }
    var c= r.c();
    if (!cc.c().name().equals(c.name())){
      var supOk= adaptedSuperTs(cc, c.name());
      if (supOk.size() == 1){ return propagateXs(xs, r, supOk.getFirst()); }
      var subOk= adaptedSuperTs(r, cc.c().name());
      if (subOk.size() == 1){ return propagateXs(xs, subOk.getFirst(), t1); }
      return qMarks(xs.size());
    }
    var res= Streams.zip(c.ts(), cc.c().ts()).map((t,ti) -> refineArg(xs, t, ti)).toList();
    return res.stream().reduce(qMarks(xs.size()), this::meet);
  }
  private List<IT> refineArg(List<String> xs, IT t, IT t1){
    var otherHead= t instanceof IT.RCC r && !(t1 instanceof IT.RCC cc && cc.c().name().equals(r.c().name()));
    return otherHead ? qMarks(xs.size()) : refine(xs, t, t1);
  }
  static <TT> List<TT> norm(List<TT> original, List<TT> candidate){
    if (candidate == original){ return original; }
    assert candidate.size() == original.size();
    for (int i : Range.of(original)){
      if (candidate.get(i) != original.get(i)){
        assert !(candidate.get(i) instanceof E || candidate.get(i) instanceof M) || !candidate.get(i).equals(original.get(i));
        return candidate;
      }
    }
    return original;
  }
  private static boolean needsPrototypeAscription(E.Literal l){
    var headKnown= !l.infName() || !l.cs().isEmpty();
    if (headKnown){ return false; }
    return l.t().undecided();
  }
  private E prototypeAscribeRootReceiver(E arg, IT expected, Optional<MName> called){
    if (!(expected instanceof IT.RCC exp)){ return arg; }
    return switch (arg){
      case E.Call c -> c.withEEs(prototypeAscribeRootReceiver(c.e(), expected, Optional.of(c.name())), c.es());
      case E.Literal l when !needsPrototypeAscription(l) -> arg;
      case E.Literal l when called.map(name -> implementable(exp.c().name()) && !declares(l, name)).orElse(true) -> l.withT(prototypeHead(exp, l.span()));
      case E.Literal l when l.ms().isEmpty() -> arg;
      case E.Literal l -> itself(l);
      default -> arg;
    };
  }
  private static boolean declares(E.Literal l, MName name){
    return l.ms().stream().map(M::sig).anyMatch(s -> s.m().equals(Optional.of(name)) && s.ret().isPresent() && s.ts().stream().allMatch(Optional::isPresent));
  }
  private boolean implementable(TName head){
    var d= meths._from(head);
    if (d == null){ return false; }
    var foreign= !head.pkgName().equals(meths.p().name());
    var foreignForbidden= foreign && (!head.isPublic() || LiteralDeclarations.has(d.cs(), LiteralDeclarations.sealed));
    return !foreignForbidden;
  }
  private E.Literal itself(E.Literal l){
    var res= new E.Literal(Optional.of(RC.imm), l.name(), l.bs(), l.cs(), l.thisName(), l.ms(), l.src(), true);
    return res.withT(preciseSelf(res).get());
  }
  private IT.RCC prototypeHead(IT.RCC expected, TSpan span){
    return new IT.RCC(expected.rc(), new IT.C(expected.c().name(), qMarks(expected.c().ts().size())), span);
  }

  private static IT normToBound(IT t, EnumSet<RC> allowed){
    if (allowed.size() == 1){ return t.withRC(allowed.iterator().next()); }
    if (!(t instanceof IT.RCC(var rc, var c, var span))){ return t; }
    var open= rc.isEmpty() || rc.get() == RC.iso && !allowed.contains(RC.iso);
    if (!open){ return t; }
    return new IT.RCC(allowed.contains(RC.imm) ? Optional.empty() : Optional.of(RC.read), c, span);
  }
  private static List<IT> normToBounds(List<B> bs, List<IT> ts){
    return Streams.zip(ts, bs).map((ti,bi) -> xName(ti).isEmpty() ? normToBound(ti, bi.rcs()) : ti).toList();
  }
  private static Optional<String> xName(IT t){ return switch (t){
    case IT.X x -> Optional.of(x.name());
    case IT.RCX(_, var x) -> Optional.of(x.name());
    case IT.ReadImmX(var x) -> Optional.of(x.name());
    default -> Optional.empty();
  };}
}