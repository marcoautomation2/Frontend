package inject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
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
import message.WellFormednessErrors;
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
- inference.E.ICall
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

public record InjectionSteps(Methods meths){
  public static List<core.E.Literal> steps(Methods meths, List<inference.E.Literal> tops){
    var s= new InjectionSteps(meths);
    assert tops.stream().allMatch(l->l.thisName().equals("this"));
    //No! at this point they have been (correctly) divided in layers assert tops.stream().sorted().toList().equals(tops);    
    return tops.stream()
      .map(l->s.stepDec(meths.cache().get(l.name()), l)).toList();
  }
  private core.E.Literal stepDec(core.E.Literal di, inference.E.Literal li){
    List<core.M> ms= li.ms().stream().map(m -> stepDecM(di, m)).toList();
    return di.withMs(ms);
  }
  private boolean sameM(core.Sig s1, inference.M.Sig s2){
    return s1.m().equals(s2.m().get()) && s1.rc().equals(s2.rc().orElse(RC.imm));
  }
  private core.M stepDecM(core.E.Literal di, inference.M m){
    core.M mCore= utils.OneOr.of("Method mismatch", di.ms().stream().filter(mi -> sameM(mi.sig(), m.sig())));
    if (m.impl().isEmpty()){ return mCore; }//assert same type as m lifted to core
    inference.E e= m.impl().get().e();
    TSpan span= di.name().approxSpan();
    List<IT> thisTypeTs= di.bs().stream().<IT>map(b -> new IT.X(b.x(),span)).toList();
    List<String> xs= m.impl().get().xs();
    var thisType= new IT.RCC(Optional.of(mCore.sig().rc()), new IT.C(di.name(), thisTypeTs),span);//no preferred on self names
    inference.E ei= meet(e, TypeRename.tToIT(mCore.sig().ret()));
    Gamma g= Gamma.of(xs, TypeRename.tToIT(mCore.sig().ts()), di.thisName(), thisType);
    ei = nextStar(Push.of(di.bs(), m.sig().bs().get()), g, ei);
    return new core.M(mCore.sig(), xs, Optional.of(new ToCore().of(ei, m.impl().get().e())));
  }
  E meet(E e, IT t){
    if (e instanceof E.Type tt){ return nextT(tt); }
    if (e instanceof E.Literal l){ if (l.t().isTV()){ return l; } }
    e = prototypeAscribeRootReceiver(e, t);
    return e.withT(meet(e.t(), t));
  }
  private long badnessAs(RCC src, TName targetHead){
    assert !src.c().name().equals(targetHead);
    var sup= adaptedSuperTs(src.rc(), src.span(), src.c().name(), src.c().ts(), targetHead);
    assert !sup.isEmpty();
    return sup.getFirst().badness();
  }
  private IT leastBad(RCC a, RCC b){
    var aSuper= isASuperB(a.c().name(), b.c().name()); // a is super of b
    var bSuper= isASuperB(b.c().name(), a.c().name()); // b is super of a
    var aBad= bSuper ? Math.max(badnessAs(a, b.c().name()),a.badness()) : a.badness();
    var bBad= aSuper ? Math.max(badnessAs(b, a.c().name()),b.badness()) : b.badness();
    //Cases considered: A[?] < B[?,?] vs B[X,?] = B[X,?] win;   A[?] < B vs A[T] = A[T] win
    var aDep= a.depth();
    var bDep= b.depth();
    if (aBad != bBad){ return aBad < bBad ? a : b; }
    if (aSuper){ return b; }
    if (bSuper){ return a; }
    if (aDep != bDep){ return aDep < bDep ? a : b; }
    return a.c().name().s().compareTo(b.c().name().s()) < 0 ? a : b;
  }
  private IT leastBad(IT a, IT b){
    assert !(a instanceof IT.U);
    assert !(b instanceof IT.U);
    if (a instanceof RCC aa && b instanceof RCC bb){ return leastBad(aa, bb); }
    if (a instanceof RCC){ return a; }
    if (b instanceof RCC){ return b; }
    if (a instanceof IT.RCX && (b instanceof IT.X | b instanceof IT.ReadImmX)){ return a; }
    if (b instanceof IT.RCX && (a instanceof IT.X | a instanceof IT.ReadImmX)){ return b; }
    return a.toString().compareTo(b.toString()) < 0 ? a: b;
  }
  IT meet(IT t1, IT t2){
    if (t2 == IT.U.Instance){ return t1; }
    if (t1 == IT.U.Instance){ return t2; }
    if (t1.equals(t2)){ return t1; }
    if (t1 instanceof IT.ReadImmX r1 && t2 instanceof IT.X x2 && r1.x().equals(x2)){ return t1; }
    if (t2 instanceof IT.ReadImmX r2 && t1 instanceof IT.X x1 && r2.x().equals(x1)){ return t2; }
    if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){
      if (!x1.c().name().equals(x2.c().name())){ return leastBad(x1,x2); }
      Optional<RC> rc= meetRcNoH(x1.rc(), x2.rc());
      return x1.withRCTs(rc,meet(x1.c().ts(), x2.c().ts()));
    }
    if (!(t1 instanceof IT.RCX x1 && t2 instanceof IT.RCX x2)){ return leastBad(t1, t2); }
    if (!x1.x().equals(x2.x())){ return leastBad(t1, t2); }
    return x1.withRC(meetRcNoH(x1.rc(), x2.rc()));
  }
  static Optional<RC> meetRcNoH(Optional<RC> a, Optional<RC> b){    
    if (a.equals(b)){ return a.map(InjectionSteps::noH); }
    if (a.isEmpty()){ return b;}
    if (b.isEmpty()){ return a;}
    if (a.get() == RC.iso){ return b.map(InjectionSteps::noH); }
    if (b.get() == RC.iso){ return a.map(InjectionSteps::noH); }
    return Optional.of(RC.imm);// returning Optional.empty(); could make it go in loop
  }
  static RC meetRcNoH(RC a, RC b){    
    if (a==b){ return noH(a); }
    if (a == RC.iso){ return noH(b); }
    if (b == RC.iso){ return noH(a); }
    return RC.imm;
  }
  static RC noH(RC a){ return a == RC.readH ? RC.read : a == RC.mutH ? RC.mut : a; }
  List<IT> meet(List<IT> t1, List<IT> t2){
    assert t1.size() == t2.size() : "should have gone in Err before";
    return IntStream.range(0, t1.size()).mapToObj(i -> meet(t1.get(i), t2.get(i))).toList();
  }
  List<IT> meet(List<List<IT>> tss){
    int size= tss.getFirst().size();
    assert tss.stream().allMatch(ts -> ts.size() == size);
    return IntStream.range(0,size)
    .mapToObj(i-> tss.stream()
      .map(ts->ts.get(i))
      .reduce((a,b)->meet(a,b))
      .orElseThrow())
    .toList();
  }
  E nextStar(List<B> bs, Gamma g, E e){
    E start = e;
    if (e.done(g)){ return e; }
    while (true){
      var s= g.snapshot();
      var oe= next(bs, g, e);
      //NOTE: very heavy assertion (recursive equals() on every fixpoint step); kept commented out as documentation of the identity-preservation invariant this loop relies on.
      //assert oe == e || !oe.equals(e) : "Allocated equal E:"+e.getClass()+"\n"+e;
      if (oe == e && !g.changed(s)){
        e.sign(g);
        assert e == start || !e.equals(start) : "Roundtrip equal E at fixpoint\nstart=" + start + "\nend=" + e;
        return e;
      }
      //if (oe.equals(e) && !g.changed(s)){ e.sign(g); return e; }//this line is useful for debugging when == gets buggy
      e = oe;
    }
  }
  private List<M> fixArity(List<M> ms, TName name, TName newName){
    if (name.equals(newName)){ return ms; }
    return norm(ms,ms.stream().map(mi->fixArity(mi, name, newName)).toList());
  }
  private List<E> nextStar(List<B> bs, Gamma g, List<E> es){
    return norm(es,es.stream().map(ei->nextStar(bs, g, ei)).toList());
  }
  private List<E> meetWithTargs(List<E> originEs,List<E> es, MSigL m, List<IT> targs){
    var res= norm(es,IntStream.range(0, es.size())
      .mapToObj(i->meet(es.get(i), m.p(i,targs))).toList());
    assert threeWayAssert(originEs, es, res); 
    return res;
  }
  private boolean threeWayAssert(List<E> originEs, List<E> es, List<E> res){
    //complex but invaluable: if it fails it means we are going 'back and forth'
    //and this could cause loops.
    IntStream.range(0,es.size()).forEach(i->{
      var e1= res.get(i);
      var e2= originEs.get(i);
      var e3= es.get(i);
      assert e1==e2 || !e1.equals(e2):" "+e1+"\n\n"+e3;
      });
    return true;
  }
  E next(List<B> bs, Gamma g, E e){
    try{
      var res= _next(bs,g,e);
      //assert meet(e.t(),res.t()).equals(res.t()): e.t()+" "+res.t();// Does not hold. How can it be?
      return res; 
    }
    catch(WellFormednessErrors.ErrToFetchContext depthErr){
      throw meths.p().err().itTooDeep(e,depthErr.c);
  }}
  E _next(List<B> bs, Gamma g, E e){ return switch (e){
    case E.X x -> nextX(bs, g, x);
    case E.Literal l -> nextL(bs, g, l);
    case E.Call c -> nextC(bs, g, c);
    case E.ICall c -> nextIC(bs, g, c);
    case E.Type c -> nextT(c);
  };}
  core.E.Literal getDec(TName name){ return meths.from(name); }
  private IT preferred(IT.RCC type){
    var d= meths._from(type.c().name());//d.cs() does contain all the transitive supertypes already.
    if (d == null){ return type; }//This can happen for {..}.foo
    var cs= d.cs().stream().filter(c -> c.name().equals(LiteralDeclarations.widen)).toList();
    if (cs.isEmpty()){ return type; }
    assert cs.size() == 1;
    assert cs.getFirst().ts().size() == 1;
    var dom= d.bs().stream().map(b -> b.x()).toList();
    IT wid= TypeRename.of(TypeRename.tToIT(cs.getFirst().ts().getFirst()), dom, type.c().ts());
    if (!(wid instanceof IT.RCC w)){ return type; }
    return new IT.RCC(type.rc(), w.c(),type.span());
  }
  private RC overloadNorm(Optional<RC> rc){ return rc.map(this::_overloadNorm).orElse(RC.imm); }
  private RC _overloadNorm(RC rc){ return switch (rc){
    case imm -> RC.imm;
    case iso -> RC.imm;
    case mut -> RC.mut;
    case mutH -> RC.mut;
    case read -> RC.read;
    case readH -> RC.read;
  };}
  private Optional<core.M> oneFromExplicitRC(List<core.M> ms){
    if (ms.size() == 1){ return Optional.of(ms.getFirst()); }
    assert ms.isEmpty() : "Ambiguous method header for explicit RC";
    return Optional.empty();
  }
  private Optional<core.M> oneFromGuessRC(List<core.M> ms, RC rc){
    if (ms.size() == 1){ return Optional.of(ms.getFirst()); }
    Optional<core.M> readOne= OneOr.opt("not well formed ms", ms.stream().filter(m -> m.sig().rc() == RC.read));
    Optional<core.M> mutOne= OneOr.opt("not well formed ms", ms.stream().filter(m -> m.sig().rc() == RC.mut));
    Optional<core.M> immOne= OneOr.opt("not well formed ms", ms.stream().filter(m -> m.sig().rc() == RC.imm));
    if (rc == RC.read){ return readOne.or(() -> immOne).or(() -> mutOne); }
    if (rc == RC.mut){ return mutOne.or(() -> readOne).or(()->immOne); }
    assert rc == RC.imm;
    return immOne.or(() -> readOne).or(()->mutOne);
  }
  public interface InstanceData<R> { R apply(IT.RCC rcc, core.E.Literal d, core.M m); }
  private <R> Optional<R> methodHeaderAnd(IT.RCC rcc, MName name, Optional<RC> favorite, InstanceData<R> f){
    var d= meths._from(rcc.c().name());
    if (d == null){ return Optional.empty(); }//case {..}.foo
    Stream<core.M> ms= d.ms().stream().filter(m -> m.sig().m().equals(name));
    Optional<core.M> om= favorite.isPresent()
        ? oneFromExplicitRC(ms.filter(mi -> mi.sig().rc().equals(favorite.get())).toList())
        : oneFromGuessRC(ms.toList(), overloadNorm(rcc.rc()));
    return om.map(mm->f.apply(rcc, d, mm));
  }
  private MSigL methodHeaderInstance(IT.RCC rcc, core.E.Literal d, core.M m){
    List<String> clsXs= d.bs().stream().map(b->b.x()).toList();
    assert clsXs.stream().distinct().count() == clsXs.size();
    List<String> methXs= m.sig().bs().stream().map(b->b.x()).toList();
    assert methXs.stream().distinct().count() == methXs.size();
    assert Collections.disjoint(clsXs, methXs);
    var clsArgs= rcc.c().ts();
    assert clsArgs.size() == clsXs.size();
    List<String> xs= Push.of(clsXs,methXs);//TODO: could avoid materializing the two lists
    List<IT> ps0= m.sig().ts().stream().map(TypeRename::tToIT).toList();
    IT ret0= TypeRename.tToIT(m.sig().ret());
    return new MSigL(m.sig().rc(), xs, d.bs(), clsArgs, m.sig().bs(), ps0, ret0);
  }
  Optional<MSigL> methodHeader(IT.RCC rcc, MName name, Optional<RC> favorite){
    return methodHeaderAnd(rcc, name, favorite, this::methodHeaderInstance);
  }
  private static List<IT> _qMarks(int n){
    return IntStream.range(0, n).<IT>mapToObj(_ -> IT.U.Instance).toList();
  }
  static List<List<IT>> smallQMarks= IntStream.range(0, 100).mapToObj(i -> _qMarks(i)).toList();// Safe: Stream.toList
  private List<IT> qMarks(int n){ return n < 100 ? smallQMarks.get(n) : _qMarks(n); }
  private List<IT> qMarks(int n, IT t, int tot){ return IntStream.range(0, tot).<IT>mapToObj(i -> i == n ? t : IT.U.Instance).toList(); }
  private E nextX(List<B> bs, Gamma g, E.X x){
    var t1Base= g.get(x.name());
    var t1= g.getWithRC(x.name());
    var t2= x.t();
    if (t1.equals(t2)){ return x; }
    if (t2 != IT.U.Instance){ updateG(g, x.name(), t1Base, t2); }
    return x.withT(meet(t1, t2));
  }
  private void updateG(Gamma g, String x, IT t1, IT t2){
    if (t1 == IT.U.Instance){ g.update(x, t2); return; }
    if (t1 instanceof IT.RCC a && t2 instanceof IT.RCC b && a.c().name().equals(b.c().name())){
      var t= new RCC(glbRcNoH(a.rc(), b.rc()), a.c(), a.span());
      if (!t.equals(t1)){ g.update(x, t); }
    }
    if (t1 instanceof IT.RCX a && t2 instanceof IT.RCX b && a.x().equals(b.x())){
      var t= a.withRC(glbRcNoH(a.rc(), b.rc()));
      if (!t.equals(t1)){ g.update(x, t); }
    }
  }
  static Optional<RC> glbRcNoH(Optional<RC> a, Optional<RC> b){
    if (a.isEmpty()){ return b; }
    if (b.isEmpty()){ return a; }
    return Optional.of(glbRcNoH(a.get(), b.get()));
  }
  static RC glbRcNoH(RC a, RC b){
    a = noH(a); b = noH(b);
    if (a == b){ return a; }
    if (a == RC.read){ return b; }
    if (b == RC.read){ return a; }
    return RC.iso;
  }
  private E nextT(E.Type t){
    if (!(t.t() instanceof IT.U)){return t; }
    return t.withT(preferred(t.type()));
  }
  private E nextIC(List<B> bs, Gamma g, E.ICall c){
    var e= nextStar(bs, g, c.e());
    var es= nextStar(bs, g, c.es());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e, es); }
    Optional<MSigL> om= methodHeader(rcc, c.name(), Optional.empty());
    if (om.isEmpty()){ return c.withEEs(e, es); }
    MSigL m= om.get();
    List<IT> ts= qMarks(m.bsArity());
    var es1= IntStream.range(0, es.size())
      .mapToObj(i->meet(es.get(i), m.p(i,ts)))
      .toList();
    var t= meet(c.t(), m.ret(ts));
    var call= new E.Call(e, c.name(), Optional.of(m.rc()), ts, es1, c.src());
    return call.withT(t);
  }
  private E nextC(List<B> bs, Gamma g, E.Call c){
    var e= nextStar(bs, g, c.e());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e, nextStar(bs, g, c.es())); }
    Optional<MSigL> om= methodHeader(rcc, c.name(), c.rc());
    if (om.isEmpty()){ return c.withEEs(e, nextStar(bs, g, c.es())); }
    MSigL m= om.get();
    var es= nextStar(bs, g, requiredOnArgs(c, m));
    assert es == c.es() || !es.equals(c.es());
    RC rc= c.rc().orElse(m.rc());
    assert m.arity() == es.size();
    List<IT> all= newAllTs(c, es, m);
    assert all.size() == m.nCls()+m.bsArity();
    List<IT> clsTs= normToBounds(m.clsBs(),all.subList(0, m.nCls()));
    List<IT> targs= normToBounds(m.methBs(),all.subList(m.nCls(), all.size()));
    e = meet(e, rcc.withTs(clsTs));
    m= m.withClsArgs(clsTs);
    var it= meet(c.t(), m.ret(targs));
    var es1= meetWithTargs(c.es(),es, m, targs);
    if (e == c.e() && es1 == c.es() && targs.equals(c.targs()) && it.equals(c.t())){ return c; }
    return c.withMore(e, rc, targs, es1, it);
  }
  private List<E> requiredOnArgs(E.Call c, MSigL m){
    List<IT> all= meet(List.of(Push.of(m.clsArgs(), MSigL.fixTargs(c.targs(), m.bsArity())), refine(m.xs(), m.ret0(), c.t())));
    var m0= m.withClsArgs(normToBounds(m.clsBs(), all.subList(0, m.nCls())));
    return meetWithTargs(c.es(), c.es(), m0, normToBounds(m.methBs(), all.subList(m.nCls(), all.size())));
  }
  private List<IT> newAllTs(E.Call c, List<E> es, MSigL m){
    List<IT> base= Push.of(m.clsArgs(), MSigL.fixTargs(c.targs(), m.bsArity()));
    if (m.bsArity() + m.clsArgs().size() == 0){ return List.of(); }//this is just an optimization
    Stream<List<IT>> a= IntStream.range(0, es.size())
      .mapToObj(i -> refine(m.xs(), m.ps0().get(i), es.get(i).t()));
    List<IT> r= refine(m.xs(), m.ret0(), c.t());
    List<List<IT>> tss= Stream.of(
      Stream.of(base),
      a,
      Stream.of(r)).flatMap(s->s).toList();
    return meet(tss);
  }
  private Optional<IT.RCC> preciseSelf(E.Literal l){
    if (l.infName() && l.rc().isEmpty()){ return Optional.empty(); }
    var xs= l.bs().stream().<IT>map(b -> new IT.X(b.x(),l.name().approxSpan())).toList();
    return Optional.of(new IT.RCC(l.rc(), new IT.C(l.name(), xs),l.name().approxSpan()));
  }
  private Optional<IT.RCC> superSelf(E.Literal l){
    if (l.cs().size() != 1){ return preciseSelf(l); }
    if (l.infName() && l.rc().isEmpty()){ return Optional.empty(); }
    return Optional.of(new IT.RCC(l.rc(), l.cs().getFirst(),l.name().approxSpan()));
  }
  TSM nextMStar(List<B> bs,Gamma g,String thisN,Optional<IT.RCC> selfPrecise,IT.RCC rcc,inference.M m){
    return m.impl().isEmpty()
      ? nextMStarAbs(rcc, m)
      : nextMStarOp(bs, g, thisN, selfPrecise, rcc, m);
    }
  private E nextL(List<B> bs, Gamma g, E.Literal l){
    var infHead= l.infHead();//infHead is set in l.withCsMs and l.withMs and l.withMsT
    // to mean the HEAD is inferred as IT.RCC and has already been used to expand methods
    var selfPrecise= preciseSelf(l);
    var selfSuper= superSelf(l);
    if (!infHead){
      if (!l.infName()){ l = l.withT(selfPrecise.get()); }
      else if (selfSuper.isPresent()){ l = l.withT(selfSuper.get()); }
      if (!(l.t() instanceof IT.RCC rcc)){ return l; }//!infHead after passing this test means right now we can expand methods
      if (!l.infName()){ l = meths.expandDeclaration(l,true); }
      else { l = meths.expandLiteral(l, rcc.c()); }
    }
    if (!(l.t() instanceof IT.RCC rcc)){ return l; }
    boolean changedMs= false;
    var res= new ArrayList<inference.M>(l.ms().size());
    List<IT> ts= rcc.c().ts();
    for (var mi : l.ms()){
      assert mi.impl().isEmpty() || selfPrecise.isEmpty() || rcc.isTV();
      TSM next= nextMStar(bs, g, l.thisName(), selfPrecise, withTsNormBs(rcc,ts), mi);
      assert next.m == mi || !next.m.equals(mi) : "Allocated equal M:\n"+mi;
      var ts1= meet(ts, next.ts);
      changedMs |= next.m != mi;
      res.add(next.m);
      ts = ts1;
    }
    if (!changedMs && ts.equals(rcc.c().ts())){ return commitToTable(g,bs, l, rcc); }
    var ms= changedMs?Collections.unmodifiableList(res):l.ms();
    IT t= withTsNormBs(rcc,ts);
    return commitToTable(g, bs, l.withMsT(ms, t), t);
  }
  private E commitToTable(Gamma g, List<B> bs, E.Literal l, IT t){
    TName name= l.name();
    if (!t.isTV() || !(t instanceof IT.RCC rcc) || hasU(l.ms()) || meths.cache().containsKey(name)){ return l; }
    var freeNames= Stream.of(
      new FreeXs(g).ftvMs(l.ms()),
      new FreeXs(g).ftvCs(l.cs()),
      new FreeXs(g).ftvT(t)
      ).flatMap(s->s);
    List<B> localBs= freeNames.distinct().map(x -> RC.get(bs, x)).toList();
    TName newName= name.withArity(localBs.size());
    List<M> ms= fixArity(l.ms(), name, newName);
    Optional<RC> orc= l.rc().or(rcc::rc);
    if (!l.infName()){
      l = new E.Literal(orc, newName, localBs, l.cs(), l.thisName(), ms, l.t(), l.src(),l.infName(), l.infHead(), l.g());
      assert !meths.cache().containsKey(name);
      var resD= meths.injectDeclaration(l);
      meths.cache().remove(name);
      meths.cache().put(resD.name(), resD);
      return l;
    }
    assert l.bs().isEmpty() : "bs must stay empty pre-commit";
    var noMeth= l.ms().stream().allMatch(m -> m.impl().isEmpty());
    if (noMeth && l.infHead() && meths._from(rcc.c().name()) != null){ return new E.Type(rcc, preferred(rcc), l.src(), l.g()); }
    var selfInferred= rcc.c().name().equals(l.name());
    List<IT.C> cs= selfInferred? meths.fetchCs(rcc.c()) : Push.of(rcc.c(), meths.fetchCs(rcc.c()));
    meths.checkMagicSupertypes(l, cs);
    assert l.infHead();
    l = new E.Literal(orc, newName, localBs, cs, l.thisName(), ms, t, l.src(),l.infName(), l.infHead(), l.g());
    core.E.Literal resD= meths.injectDeclaration(l);
    assert !meths.cache().containsKey(name);
    meths.cache().put(resD.name(), resD);
    return l;
  }
  private M fixArity(M m, TName name, TName newName){
    var s= m.sig();
    assert s.origin().isPresent();
    if (!s.origin().get().equals(name)){ return m; }
    return m.withSig(s.withOrigin(newName));
  }
  private static boolean hasU(List<inference.M> ms){
    return !ms.stream()
      .allMatch(m -> m.sig().ret().get().isTV() && m.sig().ts().stream().allMatch(t -> t.get().isTV()));
  }
  private List<Optional<IT>> updateArgs(List<String> xs, List<Optional<IT>> old, Gamma g){
    return norm(old,Streams.zip(xs, old).map((x,oi)->{
      if ("_".equals(x)){ return oi; }
      var ti= Optional.of(meet(oi.get(), g.get(x)));
      return oi.equals(ti)? oi:ti;
    }).toList());
  }
  record TSM(List<IT> ts, inference.M m){}
  TSM nextMStarAbs(IT.RCC rcc, inference.M m){
    assert m.impl().isEmpty();
    var improvedSig= m.sig();
    var omh= methodHeaderAnd(rcc, improvedSig.m().get(), improvedSig.rc(),(_,_,mi)->mi);
    assert omh.isEmpty() || assertNoBinderClash(rcc, omh.get());
    if (omh.isEmpty()){ return new TSM(rcc.c().ts(), m); }
    var rcc0= withTsNormBs(rcc,refineClsTsFromHeader(rcc.c().ts(), rcc, improvedSig, omh.get().sig()));
    var sigRes= normalizeSigAgainstHeader(rcc0, improvedSig);
    var newTs= dropMethBsFromClsTs(rcc0, improvedSig);
    if (sigRes.equals(improvedSig)){ return new TSM(newTs, m); }
    return new TSM(newTs, new inference.M(sigRes, Optional.empty()));
  }
  TSM nextMStarOp(List<B> bs, Gamma g, String thisN, Optional<IT.RCC> selfPrecise, IT.RCC rcc, inference.M m){
    assert m.impl().isPresent();
    g.newScope(m.sig().rc().get());
    g.declare(thisN, selfPrecise.<IT>map(o->o).orElse(IT.U.Instance));
    updateGWithArgs(g, m);
    var e= nextStar(Push.of(bs, m.sig().bs().get()), g, meet(m.impl().get().e(), m.sig().ret().get()));
    var args= updateArgs(m.impl().get().xs(), m.sig().ts(), g);
    g.popScope();
    return nextMStarOpRun(rcc, m, e, args);
  }
  /*The meet below narrows a method's return type to the type of its body, so a literal only ever
  gets more precise than what the use site asked for. What keeps that from destroying an invariant
  instantiation is that a decided type argument is never re-decided: requiredOnArgs and the meet in
  nextMStarOp push what is already known down before a body is inferred, and keepDecided then only
  fills the type arguments still unknown. See the five tests named in TypeSystemTest, next to
  blockLetInfersItsTypeFromTheLambdaBody, for what base needs the meet itself for.*/
  TSM nextMStarOpRun(IT.RCC rcc, inference.M m, E e, List<Optional<IT>> args){
    IT ret= meet(m.sig().ret().get(), e.t());
    M.Sig improvedSig= m.sig().withTsT(args, ret);
    var omh= methodHeaderAnd(rcc, improvedSig.m().get(), improvedSig.rc(),(_,_,mi)->mi);
    assert omh.isEmpty() || assertNoBinderClash(rcc, omh.get());
    return omh
      .map(mh->headerResult(rcc,m,e,mh.sig(),improvedSig))
      .orElseGet(()->noHeaderResult(rcc,m,e,improvedSig));
  }
  private void updateGWithArgs(Gamma g, inference.M m) {
    var xs= m.impl().get().xs();
    var args0= m.sig().ts();
    assert xs.size() == args0.size();
    assert m.sig().m().get().arity() == xs.size();
    Streams.zip(xs,args0).forEach((x,arg)->g.declare(x,arg.get()));
  }
  TSM headerResult(IT.RCC rcc, inference.M m, E e, core.Sig sig, M.Sig improvedSig){
    var rcc0= withTsNormBs(rcc,refineClsTsFromHeader(rcc.c().ts(), rcc, improvedSig,sig));
    var sigRes= normalizeSigAgainstHeader(rcc0, improvedSig);
    var impl1= m.impl().get().withE(meet(e, sigRes.ret().get()));
    var newTs= dropMethBsFromClsTs(rcc0, improvedSig);
    if (sigRes.equals(m.sig()) && impl1 == m.impl().get()){ return new TSM(newTs, m); }
    return new TSM(newTs, new inference.M(sigRes, Optional.of(impl1)));
  }
  private List<IT> refineClsTsFromHeader(List<IT> ts, IT.RCC rcc, M.Sig improvedSig, core.Sig imh){
    var Xs= getDec(rcc.c().name()).bs().stream().map(b -> b.x()).toList();
    var fromBody= meet(Stream.of(
      IntStream.range(0, imh.ts().size()).mapToObj(i -> refine(Xs,imh.ts().get(i), improvedSig.ts().get(i))),
      Stream.of(refine(Xs,imh.ret(), improvedSig.ret()))
    ).flatMap(z->z).toList());
    return Streams.zip(ts,fromBody).map(this::keepDecided).toList();
  }
  private IT keepDecided(IT decided, IT fromBody){
    if (!(decided instanceof IT.RCC a && fromBody instanceof IT.RCC b)){ return meet(decided, fromBody); }
    if (!a.c().name().equals(b.c().name())){ return decided; }
    return b.withTs(Streams.zip(a.c().ts(),b.c().ts()).map(this::keepDecided).toList());
  }
  private List<IT> refine(List<String> Xs, core.T t,Optional<IT> it){return refine(Xs,TypeRename.tToIT(t), it.get()); }
  private M.Sig normalizeSigAgainstHeader(IT.RCC rcc, M.Sig improvedSig){
    var targetBs= improvedSig.bs().isEmpty()
      ? List.<String>of()
      : improvedSig.bs().get().stream().map(B::x).toList();
    MSigL h= methodHeader(rcc, improvedSig.m().get(), improvedSig.rc()).get();
    assert h.bsArity() == targetBs.size();
    return improvedSig.withTsT(
      h.psStr(improvedSig.span(), targetBs),
      h.retStr(improvedSig.span(), targetBs));
  }
  private List<IT> dropMethBsFromClsTs(IT.RCC rcc, M.Sig improvedSig){
    var methBs= improvedSig.bs().get().stream().map(b->b.x()).toList();
    return dropMethBs(rcc.c().ts(), methBs);
  }
  private TSM noHeaderResult(IT.RCC rcc, inference.M m, E e, M.Sig improvedSig){
    var impl1= m.impl().get().withE(meet(e, improvedSig.ret().get()));
    if (improvedSig.equals(m.sig()) && impl1 == m.impl().get()){ return new TSM(rcc.c().ts(), m); }
    return new TSM(rcc.c().ts(), new inference.M(improvedSig, Optional.of(impl1)));
  }
  List<IT> dropMethBs(List<IT> ts, List<String> methBs){
    if (methBs.isEmpty()){ return ts; }
    return norm(ts,ts.stream().map(t->dropMethBs(t, methBs)).toList());
  }
  IT dropMethBs(IT t, List<String> methBs){ return switch (t){
    case IT.X x -> methBs.contains(x.name()) ? IT.U.Instance : t;
    case IT.RCX(_,var x) -> methBs.contains(x.name()) ? IT.U.Instance : t;
    case IT.ReadImmX(var x) -> methBs.contains(x.name()) ? IT.U.Instance : t;
    case IT.RCC rcc -> withTsNormBs(rcc,dropMethBs(rcc.c().ts(), methBs));
    case IT.U _ -> t;
  };}
  private boolean assertNoBinderClash(IT.RCC rcc, core.M m){
    var cls= getDec(rcc.c().name()).bs().stream().map(B::x).toList();
    var meth= m.sig().bs().stream().map(B::x).toList();
    return Collections.disjoint(cls, meth);
  }
  List<IT> refine(List<String> xs, IT t, IT t1){
    if (t1 instanceof IT.U){ return qMarks(xs.size()); }
    return switch (t){
      case IT.X x -> refineXs(xs, x, t1);
      case IT.RCX(RC _, IT.X x) -> refineXs(xs, x, stripRCAlsoThisSide(t1));
      case IT.ReadImmX(IT.X x) -> refineXs(xs, x, stripRCAlsoThisSide(t1));
      case IT.RCC(_, IT.C c,_) -> propagateXs(xs, c, t1);
      case IT.U _ -> qMarks(xs.size()); //stripRCAlsoThisSide is needed to distinguish
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
    case IT.RCC rcc -> rcc.withRC(RC.iso);//This iso is because on conflict iso is the first to disappear? 
    case IT.U _ -> IT.U.Instance;
  };}
  List<IT> refineXs(List<String> xs, IT.X x, IT t1){
    var i= xs.indexOf(x.name());
    if (i == -1 ){ return qMarks(xs.size()); }
    return qMarks(i, t1, xs.size());
  }
  private boolean isASuperB(TName a, TName b){
    var d= meths._from(b);
    if (d == null){ return false; } // {..}.foo etc.
    return d.cs().stream().anyMatch(c->c.name().equals(a));
  }
  private List<IT.RCC> adaptedSuperTs(Optional<RC> rc,TSpan span, TName source,List<IT> ts, TName target){
    var d= meths._from(source);
    if (d == null){ return List.of(); } // {..}.foo etc.
    List<String> xs= d.bs().stream().map(B::x).toList();
    return d.cs().stream()
      .filter(sc -> sc.name().equals(target))
      .distinct()
      .map(ci->new IT.RCC(rc, TypeRename.tcToITC(ci),span))
      .map(rcc->(IT.RCC)TypeRename.of(rcc, xs, ts))
      .toList();
  }  
  List<IT> propagateXs(List<String> xs, IT.C c, IT t1){
    if (t1 instanceof IT.U){ return qMarks(xs.size()); }
    if (!(t1 instanceof IT.RCC cc)){ return qMarks(xs.size()); }
    if (!cc.c().name().equals(c.name())){
      var supOk= adaptedSuperTs(cc.rc(),cc.span(),cc.c().name(),cc.c().ts(),c.name());
      if (!supOk.isEmpty()){ return propagateXs(xs,c,supOk.getFirst()); }
      var subOk= adaptedSuperTs(cc.rc(),cc.span(),c.name(),c.ts(),cc.c().name());
      if (!subOk.isEmpty()){ return propagateXs(xs,subOk.getFirst().c(),t1); }
      return qMarks(xs.size());
    }
    assert cc.c().ts().size() == c.ts().size();
    List<List<IT>> res= IntStream.range(0, c.ts().size())
      .mapToObj(i -> refine(xs, c.ts().get(i), cc.c().ts().get(i))).toList();
    return res.isEmpty() ? qMarks(xs.size()) : meet(res);
  }
  static boolean assertEqEM(Object o1, Object o2){
     if(!( o1 instanceof E || o1 instanceof M)){ return true; }
     return o1==o2 || !o1.equals(o2);
    }
  static <TT> List<TT> norm(List<TT> original, List<TT> candidate){
    if (candidate == original){ return original; }
    int n= original.size();
    assert candidate.size() == n;
    for (int i : Range.of(original)){
      if (candidate.get(i) != original.get(i)){
        assert assertEqEM(candidate.get(i), original.get(i));
        return candidate; 
      }
    }
    return original;
  }
  private static boolean needsPrototypeAscription(E.Literal l){
    if (l.infHead() || !l.infName() || !l.cs().isEmpty()){ return false; }
    return (l.t() instanceof IT.U /*&& l.ms().stream().anyMatch(m-> !m.sig().isFull())*/);
  }
  private E prototypeAscribeRootReceiver(E arg, IT expected){
    if (!(expected instanceof IT.RCC exp)){ return arg; }
    return switch (arg){
      case E.Call c -> c.withE(prototypeAscribeRootReceiver(c.e(), expected));
      case E.ICall c -> c.withE(prototypeAscribeRootReceiver(c.e(), expected));
      case E.Literal l -> needsPrototypeAscription(l)
        ? l.withT(prototypeHead(exp,l.span()))
        : arg;
      default -> arg;
    };
  }
  private IT.RCC prototypeHead(IT.RCC expected, TSpan span){
    return new IT.RCC(expected.rc(), new IT.C(expected.c().name(), qMarks(expected.c().ts().size())), span);
  }
   
  private static IT normToBound(IT t, EnumSet<RC> allowed){
    if (allowed.size() == 1){ return t.withRC(allowed.iterator().next()); }
    return t;
  }
  static List<IT> normToBounds(List<B> bs, List<IT> ts){
    if (bs.size() != ts.size()){ return ts; }
    return Streams.zip(ts,bs).map((ti,bi)->normToBound(ti,bi.rcs())).toList();
  }
  private IT.RCC withTsNormBs(IT.RCC rcc, List<IT> ts){
    var d= meths._from(rcc.c().name());
    if (d == null){ return rcc.withTs(ts); }   // {..}.foo etc.
    return rcc.withTs(normToBounds(d.bs(), ts));
  }
}

record MSigL(RC rc, List<String> xs, List<B> clsBs, List<IT> clsArgs, List<B> methBs, List<IT> ps0, IT ret0){
  int arity(){ return ps0.size(); }
  int nCls(){ return clsArgs.size(); }
  int bsArity(){ return methBs.size(); }
  List<String> methXs(){ return xs.subList(nCls(), xs.size()); }

  IT p(int i, List<IT> targs){ return inst(ps0.get(i), targs); }
  IT ret(List<IT> targs){ return inst(ret0, targs); }

  MSigL withClsArgs(List<IT> clsArgs){
    if (clsArgs.equals(this.clsArgs)){ return this; }
    assert clsArgs.size() == this.clsArgs.size();
    return new MSigL(rc, xs, clsBs, clsArgs, methBs, ps0, ret0);
  }

  private IT inst(IT t, List<IT> targs){//Note: this will eventually become an error at type system time.
    targs = fixTargs(targs, bsArity());
    var ts= Push.of(clsArgs,targs);//performance? we could cache this result since targs is fixed and used over and over
    return TypeRename.of(t, xs, ts);
  }
  static IT arityErr(){ return IT.U.Instance; }
  static List<IT> fixTargs(List<IT> targs, int n){
    int k= targs.size();
    if (k == n){ return targs; }
    if (k > n){ return targs.subList(0, n); }
    return Stream.concat(
      targs.stream(),
      IntStream.range(0, n-k).mapToObj(_->arityErr())
      ).toList();
  }
  IT pStr(TSpan span, int i, List<String> targetBs){ return inst(ps0.get(i), toXs(span,targetBs)); }
  List<Optional<IT>> psStr(TSpan span,List<String> targetBs){
    assert targetBs.size() == bsArity();
    var ts= toXs(span, targetBs);
    return ps0.stream().map(p->Optional.of(inst(p, ts))).toList();
  }
  IT retStr(TSpan span,List<String> targetBs){
    assert targetBs.size() == bsArity();
    return inst(ret0, toXs(span,targetBs));
  }
  private List<IT> toXs(TSpan span,List<String> targetBs){ return targetBs.stream().<IT>map(n->new IT.X(n,span)).toList(); }
}