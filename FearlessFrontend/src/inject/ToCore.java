package inject;

import java.util.*;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.B;
import core.LiteralDeclarations;
import core.MName;
import core.RC;
import core.Src;
import core.T;
import core.TName;
import core.TSpan;
import inference.Gamma;
import inference.IT;
import offensiveUtils.EqTransparent;
import utils.Bug;
import utils.OneOr;
import utils.Pos;
import utils.Push;
import utils.Streams;

public record ToCore(List<B> ctx, List<ToCore.Enclosing> enclosing, Methods meths){
  public record Enclosing(List<TName> parents, core.Sig sig){}
  core.E of(inference.E exp, inference.E orig){ return switch (exp){
    case inference.E.X(var name, _, var src, _) -> new core.E.X(name, src);
    case inference.E.Type(var type, _, var src, _) -> type(type, src);
    case inference.E.Literal le -> literal(le, orig);
    case inference.E.Call ce -> call(ce, callLike(orig, ce.name()));
  };}
  private boolean inScope(List<IT> ts){ return ts.stream().flatMap(IT::ftv).allMatch(B.xs(ctx)::contains); }
  core.E.Type type(IT.RCC type, Src src){
    assert inScope(List.of(type));
    return new core.E.Type(new T.RCC(type.rc().orElse(RC.imm), TypeRename.itcToTC(type.c()), type.span()), src);
  }
  core.E.Literal literal(inference.E.Literal e, inference.E orig){
    var o= (inference.E.Literal)orig;
    assert o.src() == e.src();
    var rc= e.rc().orElse(RC.imm);
    assert o.infName() == e.infName();
    assert o.infName() || e.name().equals(o.name());
    assert e.thisName().equals(o.thisName());
    var free= new FreeXs(new Gamma());
    var bs= !e.infName() ? e.bs() : Streams.of(B.xs(e.bs()).stream(), free.ftvCs(e.cs()), free.ftvMs(e.ms()), free.ftvMs(o.ms())).distinct().map(x -> B.get(ctx, x)).toList();
    assert !e.infName() || B.xs(ctx).containsAll(B.xs(bs));
    var name= e.name().withArity(bs.size());
    var inner= new ToCore(e.infName() ? Push.of(ctx, bs).stream().distinct().toList() : bs, enclosing, meths);
    if (!(e.t() instanceof IT.RCC) && !e.t().undecided()){ throw meths.p().err().literalImplementsTypeParameter(e, e.t(), enclosing, meths::from); }
    var csIT= distinctTypes(inner.ctx(), Push.of(o.cs(), e.cs()));
    for (var c : csIT){ checkHead(e, c); }
    assert !e.infName() || !e.thisName().equals("_") || e.t().undecided() || e.ms().stream().anyMatch(m -> m.impl().isPresent());
    var ms= inner.mapMs(e.ms(), o.ms(), e).stream().map(m -> withOrigin(m, e.name(), name)).toList();
    var cs= TypeRename.itcToTC(csIT);
    assert InjectionToInferenceVisitor.duplicatedSupertypes(inner.ctx(), csIT).isEmpty();
    return new core.E.Literal(rc, name, bs, cs, e.thisName(), ms, e.src(), e.infName());
  }
  static List<IT.C> distinctTypes(List<B> bs, List<IT.C> cs){
    var res= new ArrayList<IT.C>();
    for (var c : cs){ if (res.stream().noneMatch(r -> sameType(bs, r, c))){ res.add(c); } }
    return Collections.unmodifiableList(res);
  }
  static boolean sameType(List<B> bs, IT.C a, IT.C b){
    var span= TSpan.fromPos(Pos.unknown);
    return TypeRename.eqModXRC(bs, new IT.RCC(Optional.of(RC.imm), a, span), new IT.RCC(Optional.of(RC.imm), b, span));
  }
  private static core.M withOrigin(core.M m, TName from, TName to){
    var s= m.sig();
    if (!s.origin().equals(from)){ return m; }
    return m.withSig(new core.Sig(s.rc(), s.m(), s.bs(), s.ts(), s.ret(), to, s.abs(), s.span()));
  }

  private List<core.E> mapArgs(List<inference.E> es, List<inference.E> oEs){ return Streams.zip(es, oEs).map(this::of).toList(); }
  core.E.Call call(inference.E.Call e, CallLike o){
    var rc= e.rc().orElse(RC.imm);
    var targs= InjectionSteps.writtenTargs(e) ? o.targs : e.targs();
    assert inScope(targs);
    var recv= of(e.e(), o.e);
    var fixed= IntStream.range(0, targs.size()).mapToObj(i -> targ(e, targs, i)).toList();
    var args= mapArgs(e.es(), o.es);
    return new core.E.Call(recv, e.name(), rc, TypeRename.itToT(fixed), args, new EqTransparent<>(null), e.src());
  }
  private IT targ(inference.E.Call e, List<IT> targs, int i){
    var t= targs.get(i);
    if (t.isTV()){ return t; }
    var b= methodSig(e).bs().get(i);
    var amb= ambs(t).findFirst();
    if (amb.isEmpty()){ return fillVoid(t, b); }
    var cs= amb.get().candidates().stream().map(c -> replace(t, amb.get(), c)).toList();
    var common= t instanceof IT.Amb ? withinBound(meths.commonSupertypes(cs), b) : List.<IT.RCC>of();
    var err= meths.p().err();
    throw err.typeArgAmbiguous(e, b.x(), cs, common, err.callWithTargs(e, targs, i), meths::_from);
  }
  private static Stream<IT.Amb> ambs(IT t){ return switch (t){
    case IT.Amb a -> Stream.of(a);
    case IT.RCC rcc -> rcc.c().ts().stream().flatMap(ToCore::ambs);
    default -> Stream.of();
  };}
  private static IT replace(IT t, IT from, IT to){
    if (t == from){ return to; }
    if (!(t instanceof IT.RCC rcc)){ return t; }
    return rcc.withTs(rcc.c().ts().stream().map(ti -> replace(ti, from, to)).toList());
  }
  private static IT voidT(B b){ return new IT.RCC(Optional.of(b.rcs().iterator().next()), new IT.C(LiteralDeclarations.baseVoid, List.of()), TSpan.fromPos(Pos.unknown)); }
  private IT fillVoid(IT t, B b){ return switch (t){
    case IT.U _ -> voidT(b);
    case IT.RCC rcc -> rcc.withTs(Streams.zip(rcc.c().ts(), meths.from(rcc.c().name()).bs()).map(this::fillVoid).toList());
    case IT.Amb _ -> throw Bug.unreachable();
    default -> t;
  };}
  private core.Sig methodSig(inference.E.Call e){
    var d= meths.from(((IT.RCC)e.e().t()).c().name());
    return OneOr.of("Method of a call with inferred type arguments", d.ms().stream().map(core.M::sig).filter(s -> s.m().equals(e.name()) && s.rc() == e.rc().get()));
  }
  private void checkHead(inference.E.Literal e, IT.C c){
    var unknown= IntStream.range(0, c.ts().size()).filter(i -> !c.ts().get(i).isTV()).boxed().toList();
    if (unknown.isEmpty()){ return; }
    calls(e).forEach(this::targs);
    var bs= meths.from(c.name()).bs();
    var xs= B.xs(bs);
    var head= e.t() instanceof IT.RCC t && t.c().name().equals(c.name()) ? t.c() : c;
    for (int i : unknown){ if (head.ts().get(i) instanceof IT.Amb(var cs)){ throw meths.p().err().literalHeadAmbiguous(e, head, i, xs.get(i), cs, withinBound(meths.commonSupertypes(cs), bs.get(i)), meths::_from); } }
    throw meths.p().err().literalHeadNotInferred(e, c, unknown, xs);
  }
  private static List<IT.RCC> withinBound(List<IT.RCC> ts, B b){ return ts.stream().filter(t -> t.rc().map(b.rcs()::contains).orElse(true)).toList(); }
  private void targs(inference.E.Call c){ IntStream.range(0, c.targs().size()).forEach(i -> targ(c, c.targs(), i)); }
  private static Stream<inference.E.Call> calls(inference.E e){ return switch (e){
    case inference.E.Call c -> Streams.of(calls(c.e()), Stream.of(c), c.es().stream().flatMap(ToCore::calls));
    case inference.E.Literal l -> l.ms().stream().flatMap(m -> m.impl().stream()).flatMap(i -> calls(i.e()));
    case inference.E.X _, inference.E.Type _ -> Stream.of();
  };}
  private List<core.M> mapMs(List<inference.M> es, List<inference.M> os, inference.E.Literal at){
    return es.stream()
      .map(me -> m(me, me.impl().isEmpty() ? me : matchM(os, me), at))
      .toList();
  }
  private static inference.M matchM(List<inference.M> os, inference.M e){
    var s= e.sig().span();
    return OneOr.of("Failing to connect methods @"+s, os.stream().filter(o -> o.sig().span() == s));
  }
  private core.M m(inference.M e, inference.M o, inference.E.Literal at){
    var s= sig(e.sig(), o.sig(), at);
    if (e.impl().isEmpty()){
      assert o.impl().isEmpty();
      return new core.M(s, e.xs(), e.names(), Optional.empty());
    }
    var ei= e.impl().get();
    var oi= o.impl().get();
    var inner= new ToCore(Push.of(ctx, s.bs()).stream().distinct().toList(), Push.of(enclosing, new Enclosing(at.cs().stream().map(IT.C::name).toList(), s)), meths);
    return new core.M(s, e.xs(), e.names(), Optional.of(inner.of(ei.e(), oi.e())));
  }
  core.Sig sig(inference.M.Sig inf, inference.M.Sig usr, inference.E.Literal at){
    var ts= Streams.zip(usr.ts(), inf.ts()).map((u,i) -> u.or(() -> i)).toList();
    var ret= usr.ret().or(inf::ret);
    var rc= usr.rc().or(inf::rc).orElse(RC.imm);
    var m= usr.m().or(inf::m);
    var origin= usr.origin().or(inf::origin);
    if (m.isEmpty() || origin.isEmpty()){ throw meths.p().err().methodNotInferred(at, usr); }
    for (int i= 0; i < ts.size(); i += 1){ if (!decided(ts.get(i))){ throw meths.p().err().methodTypeNotInferred(at, usr, m.get(), "parameter "+(i+1)); } }
    if (!decided(ret)){ throw meths.p().err().methodTypeNotInferred(at, usr, m.get(), "the result"); }
    var bs= usr.bs().or(inf::bs).orElse(List.of());
    return new core.Sig(rc, m.get(), bs, ts.stream().map(TypeRename::itToT).toList(), TypeRename.itToT(ret), origin.get(), usr.abs(), usr.span());
  }
  private static boolean decided(Optional<IT> t){ return t.filter(IT::isTV).isPresent(); }
  private record CallLike(inference.E e, List<inference.E> es, List<IT> targs){}
  private static CallLike callLike(inference.E o, MName name){
    return switch (o){
      case inference.E.Call(var e, var n, _, var targs, var es, _, _, _) when n.equals(name) -> new CallLike(e, es, targs);
      default -> throw Bug.unreachable();
    };
  }

  private static final Optional<core.E> syntheticBody= Optional.of(new core.E.X("this", Src.synthetic));
  core.M mSynthetic(inference.M m){
    var s= sig(m.sig(), m.sig(), null);
    return new core.M(s, m.xs(), m.names(), m.impl().isEmpty() ? Optional.empty() : syntheticBody);
  }
}