package typeSystem;

import static core.RC.*;

import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.function.Function;
import java.util.stream.Collectors;

import core.AllLs;
import core.B;
import core.E;
import core.FearlessException;
import core.LiteralDeclarations;
import core.M;
import core.MName;
import core.OtherPackages;
import core.RC;
import core.Sig;
import core.T;
import core.TName;
import core.TSpan;
import inject.TypeRename;
import message.Err;
import message.Reason;
import message.TypeSystemErrors;
import utils.OneOr;
import utils.Push;
import utils.Range;
import utils.Streams;
import utils.UriSort;
import core.E.*;
import pkgmerge.Package;

public record TypeSystem(TypeScope scope, ViewPointAdaptation v){
  Kinding k(){ return v.k(); }
  public TypeSystemErrors tsE(){ return v.k().tsE(); }
  public Err err(){ return v.k().tsE().err(); }
  public Function<TName,Literal> decs(){ return v.k().tsE().decs(); }
  public record TRequirement(String reqName,T t){}
  public record MType(String promotion,RC rc,List<T> ts,T t){
    MType withPromotion(String promotion){ return new MType(promotion,rc,ts,t); }
  }
  List<MType> multiMeth(List<B> bs1, MType mType){ return MultiMeth.of(bs1,mType); }

  public static void allOk(List<Literal> tops, Package pkg, OtherPackages other){
    tops= UriSort.byFolderThenFile(tops, l->l.span().inner.fileName());
    assert core.AssertNoRepeatedTypeNames.ok(tops);
    Map<TName,Literal> map= AllLs.of(tops);
    Function<TName,Literal> decs= n->LiteralDeclarations._from(n,map::get,other);
    Map<String,String> invMap= pkg.map().entrySet().stream()
      .collect(Collectors.toUnmodifiableMap (Map.Entry::getValue, Map.Entry::getKey));
    var ts= new TypeSystem(TypeScope.top(), new ViewPointAdaptation(new Kinding(new TypeSystemErrors(decs,pkg,invMap))));
    tops.forEach(l->ts.litOk(Gamma.empty(),l));
  }
  public boolean isSub(List<B> bs, T t1, T t2){
    return t1.equals(t2)
      || isXReadImmXSubtype(bs,t1,t2)
      || isSameShapeSubtype(bs,t1,t2)
      || isImplSubtype(bs,t1,t2);
  }
  public void check(List<B> bs, Gamma g, E e, T expected){
    var rs= List.of(new TRequirement("", expected));
    var out= typeOf(bs,g,e,rs);
    assert out.size() == 1;
    var got= out.getFirst();
    if (got.isEmpty()){ return; }
    throw tsE().methBodyWrongType((TypeScope.Method)scope,e,got,expected);
  }
  List<Reason> typeOf(List<B> bs, Gamma g, E e, List<TRequirement> rs){ return switch(e){
    case X x -> checkX(bs,g,x,rs);
    case Type t -> checkType(bs,g,t,rs);
    case Literal l -> checkLiteral(bs,g,l,rs);
    case Call c -> checkCall(bs,g,c,rs);
  };}
  private List<Reason> checkX(List<B> bs, Gamma g, X x, List<TRequirement> rs){
    var b= g.bind(x.name());
    T declared= b.declared();
    var cur= b.current();
    if (!(cur instanceof Change.WithT w)){ throw tsE().parameterNotAvailableHere(x, declared, (Change.NoT)cur, bs); }
    T got= w.currentT();
    if (rs.isEmpty()){ return List.of(Reason.pass(got)); }
    return rs.stream().<Reason>map(r->{
      if (isSub(bs,got,r.t())){ return Reason.pass(got); }
      boolean declaredOk= isSub(bs,declared,r.t());
      return Reason.parameterDoesNotHaveRequiredTypeHere(this,x, bs, r, declared, w, declaredOk);
    }).toList();
  }
  private List<Reason> checkType(List<B> bs, Gamma g, Type t, List<TRequirement> rs){
    k().check(t,bs,t.type());
    var ll= decs().apply(t.type().c().name());
    if (!hasInstance(ll)){ throw tsE().typeDeclaredInMethod(t, ll); }
    var getIso= (readOrImm(t.type().rc()) && !hasAbstractMut(ll)) || mutOrMutH(t.type().rc());
    var l= ll.withRC(getIso ? RC.iso : t.type().rc());
    var tt= getIso ? new Type(t.type().withRC(RC.iso), t.src()) : t;
    l.ms().forEach(m->checkImplemented(l,m,tt));
    return reqs(t,bs,tt.type(),rs);//reqs correctly used for two similar things
  }
  private static boolean hasInstance(Literal l){
    return l.thisName().equals("this") || LiteralDeclarations.has(l.cs(), LiteralDeclarations.captureFree);
  }
  private static boolean readOrImm(RC rc){ return rc == RC.read || rc == RC.imm; }
  private static boolean mutOrMutH(RC rc){ return rc == RC.mut || rc == RC.mutH; }
  private static boolean hasAbstractMut(Literal l){ return l.ms().stream().anyMatch(m->m.sig().abs() && m.sig().rc() == RC.mut); }
  private List<Reason> reqs(E blame, List<B> bs, T got, List<TRequirement> rs){
    if (rs.isEmpty()){ return List.of(Reason.pass(got)); }
    return rs.stream().map(r->isSub(bs,got,r.t())
      ? Reason.pass(got)
      : Reason.literalDoesNotHaveRequiredType(this,blame,bs,got,r.t())
      ).toList();    
  }
  private List<Reason> checkLiteral(List<B> bs1, Gamma g, Literal _l, List<TRequirement> rs){
    var span= _l.name().approxSpan();
    var getIso= ((readOrImm(_l.rc()) && !hasAbstractMut(_l)) || _l.rc() == mut)
      && _l.thisName().equals("_")
      && new FreeMutyParameters(bs1,g).isFree(_l);
    var l= getIso ? _l.withRC(RC.iso) : _l;
    var ts= l.bs().stream().<T>map(b->new T.X(b.x(),span)).toList();
    var ms= l.ms().stream().filter(m->m.sig().origin().equals(l.name())).toList();
    var thisType= new T.RCC(l.rc(),new T.C(l.name(),ts),span);
    assert l.bs().stream().allMatch(b->bs1.stream().anyMatch(b1->b.x().equals(b1.x()))):l.bs()+" "+bs1;
    k().check(l,bs1,thisType);
    litOk(g.filterFTV(l),l);
    ms.forEach(m->checkCallable(l,m));
    l.ms().forEach(m->checkImplemented(l,m,l));
    return reqs(l,bs1,thisType,rs);
  }
  private List<Reason> checkCall(List<B> bs,Gamma g,Call c, List<TRequirement> rs){
    return new CallTyping(this,bs,g,c,rs).run();
  }
  private void checkImplemented(Literal l, M m,E blame){
    if (!m.sig().abs()){ return; }
    if (!callable(l.rc(),m.sig().rc())){ return; }
    throw tsE().callableMethodStillAbstract(blame,m, l);
  }
  private void checkCallable(Literal l, M m){
    RC litRC= l.rc();
    if (callable(litRC,m.sig().rc())){ return; }
    throw tsE().methodImplementationDeadCode(m.sig().span(), m, l);
  }
  private boolean callable(RC litRC, RC recRc){ return recRc != RC.mut || (litRC != RC.imm && litRC !=RC.read); }

  private record Key(MName m, RC rc){}
  //Sources is needed, not assert only: the user can simply try to override with a non subtype signature.
  //l.ms is the resolved set, either inferred or resolved by hand in a wrong way.
  SequencedMap<Key,List<Sig>> sources(Literal l){
  return Sources.collect(this, l).stream()
    .collect(Collectors.groupingBy(s -> new Key(s.m(), s.rc()),LinkedHashMap::new,Collectors.toList()));
  }
  private static final MName asOne= new MName(".as",1);
  private void baseIdOk(Literal l){
    if (!LiteralDeclarations.has(l.cs(),LiteralDeclarations.baseId)){ return; }
    var m= OneOr.of("BaseId literals declare only #",l.ms().stream());
    if (m.e().isPresent() && !isId(m)){ throw tsE().baseIdBadBody(l,m); }
  }
  private boolean isId(M m){
    assert m.xs().size() == 1;
    var x= m.xs().getFirst();
    return switch(m.e().get()){
      case X e -> e.name().equals(x);
      case Call c -> c.e() instanceof X e && e.name().equals(x) && c.name().equals(asOne)
        && isBaseContainer(m.sig().ts().getFirst());
      default -> false;
    };
  }
  private boolean isBaseContainer(T t){
    return t instanceof T.RCC rcc
      && LiteralDeclarations.has(decs().apply(rcc.c().name()).cs(),LiteralDeclarations.baseContainer);
  }
  private void litOk(Gamma g, Literal l){
    baseIdOk(l);
    var delta= l.bs();
    var span= l.name().approxSpan();
    var selfT= new T.C(l.name(),dom(delta,span));
    SequencedMap<Key,List<Sig>> sources= sources(l);
    sources.forEach((k,group)->methodTableOk(l,k,group));
    l.cs().forEach(c->csOk(l,delta,c));
    var g1= g.add(l.thisName(),new T.RCC(l.rc().isoToMut(),selfT,span));
    l.ms().forEach(m->{
      Gamma g2= v().of(g1,l,m);//passing l and m instead of their RC for better errors
      methOk(l,delta,g2,m);
    });
  }
  private void csOk(Literal l, List<B> delta, T.C c){
    k().checkC(l,delta,c);
    var d= decs().apply(c.name());
    if (!hasInstance(d)){ throw tsE().typeDeclaredInMethod(l, d); }
  }
  private void methOk(Literal forErr,List<B> delta, Gamma g, M m){
    var allBs= Push.of(delta,m.sig().bs());
    m.sig().ts().forEach(t->k().check(forErr,allBs,t));
    k().check(forErr,allBs,m.sig().ret());
    if(m.e().isEmpty()){ return; }
    try{ bodyOk(forErr,allBs,g,m); }
    catch(FearlessException fe){ throw tsE().mCallFrame(m, fe); }
  }
  private void bodyOk(Literal forErr,List<B> delta, Gamma g, M m){
    var ts= m.sig().ts();
    var xs= m.xs();
    g= g.addAll(ts, xs);//Note: 'this' already in g1
    var t= new TypeSystem(scope.pushM(forErr, m),v);
    t.check(delta,g,m.e().get(),m.sig().ret());
    Streams.zip(xs,ts).forEach((x,tx)->{
      if (!k().of(delta,tx,EnumSet.of(mut,read,mutH,readH,imm))){ Affine.usedOnce(tsE(),forErr,m,x,m.e().get()); }
    });
  }  
  private List<T> dom(List<B> bs,TSpan span){ return bs.stream().<T>map(b->new T.X(b.x(),span)).toList(); }
  
  private boolean isImplSubtype(List<B> bs, T t1, T t2){
    if (!(t1 instanceof T.RCC rcc1)){ return false; }
    Literal d= decs().apply(rcc1.c().name());
    assert d!=null: rcc1;
    List<String> xs= d.bs().stream().map(B::x).toList();
    for (T.C ci : d.cs()){
      T sup= TypeRename.of(new T.RCC(rcc1.rc(), ci,rcc1.span()), xs, rcc1.c().ts());
      if (isSub(bs, sup, t2)){ return true; }
    }
    return false;
  }
  private boolean isXReadImmXSubtype(List<B> bs, T t1, T t2){
    return t2 instanceof T.ReadImmX rix
      && t1 instanceof T.X x
      && rix.x().name().equals(x.name())
      && k().of(bs, x, EnumSet.of(iso,imm,mut,read));
  }
  private boolean isSameShapeSubtype(List<B> bs, T t1, T t2){
    if(!eqModXRC(bs,t1.withRC(mut),t2.withRC(mut))){ return false; }
    var rcs1= intrinsicRCs(bs, t1);
    var rcs2= intrinsicRCs(bs, t2);
    for (var r1 : rcs1){
      for (var r2 : rcs2){
        if (!r1.isSubType(r2)){ return false; }
      }
    }
    return true;
  }
  EnumSet<RC> intrinsicRCs(List<B> bs, T t){ return switch(t){
    case T.RCC(var rc, _,_) -> EnumSet.of(rc);
    case T.RCX(var rc, _) -> EnumSet.of(rc);
    case T.X(var x,_) -> get(bs, x).rcs();
    case T.ReadImmX x -> intrinsicRCs(bs,x);
  };}
  private EnumSet<RC> intrinsicRCs(List<B> bs, T.ReadImmX x){
    var rcs= get(bs, x.x().name()).rcs();
    if (EnumSet.of(iso, imm).containsAll(rcs)){ return EnumSet.of(imm); }
    if (EnumSet.of(mut, mutH, read, readH).containsAll(rcs)){ return EnumSet.of(read); }
    return EnumSet.of(read, imm);
  }
  private static Sig findCanonical(Literal l, MName name, RC rc){
    return OneOr.of("Missing or Duplicate meth",l.ms().stream().map(M::sig).filter(s->s.m().equals(name) && s.rc() == rc));
  }
  private void methodTableOk(Literal l,Key k,List<Sig> group){
    Sig chosen= findCanonical(l,k.m(),k.rc());
    assert group.stream().allMatch(s->s.m().equals(chosen.m()) && s.rc()== chosen.rc());
    assert mostSpecificByOrigin(group,chosen);
    assert absPreserved(chosen);//This assert and the one below do the same thing in working programs but may differ in buggy ones
    assert group.stream().filter(s->s.origin().equals(chosen.origin())).allMatch(s->chosen.abs() == s.abs());
    for(var s:group){ sigSub(l,chosen,s); }
    assert concreteConflictsSolved(group,chosen);
  }
  private boolean concreteConflictsSolved(List<Sig> group,Sig chosen){
    return group.stream().filter(s->!s.abs())
      .allMatch(s->isOriginSub(chosen.origin(),s.origin()));
  }
  private boolean mostSpecificByOrigin(List<Sig> group, Sig chosen){
    for (var s : group){
      if (s.equals(chosen)){ continue; }
      assert !s.origin().equals(chosen.origin()):
        s+" "+chosen+"""        
        The assert above is actually a big deal. It can logically break in an better version of Fearless
        when inference would know about subtypes when selecting the 'chosen'.
        Same origin can appear multiple times when the same generic supertype is inherited with
        different instantiation arguments (Fearless allows this; Java forbids it).
        Currently, Fearless requires the programmer to select a winning signature by overriding it.
        """;
      assert !isOriginSub(s.origin(),chosen.origin()) : "Resolver not most specific: chosen "+chosen.origin().s()+" but "+s.origin().s()+" exists";
    }
    return true;
  }
  private boolean absPreserved(Sig chosen){
    Literal o= decs().apply(chosen.origin());
    Sig src= findCanonical(o,chosen.m(),chosen.rc());
    assert !src.abs() || chosen.abs():"Abstractness mismatch";
    return true;
  }  
  private boolean isOriginSub(TName sub, TName sup){
    if (sub.equals(sup)){ return true; }
    Literal d= decs().apply(sub);
    for (var parent : d.cs()){ if (isOriginSub(parent.name(), sup)){ return true; } }
    return false;
  }
  private void sigSub(Literal l, Sig current, Sig parent){
    assert current.bs().equals(parent.bs());
    List<B> ctx= Push.of(l.bs(),current.bs());
    int tsSize= current.ts().size();
    assert tsSize == parent.ts().size():"Arity encoded in meth name";
    for (int i : Range.of(0,tsSize)){
      var badArg= !isSub(ctx, parent.ts().get(i), current.ts().get(i));
      if (badArg){ throw tsE().methodOverrideSignatureMismatchContravariance(this,ctx,l,current,parent, i); }
    }
    var badRet= !isSub(ctx, current.ret(), parent.ret());
    if (badRet){ throw tsE().methodOverrideSignatureMismatchCovariance(this,ctx,l,current,parent); }
  }
  private boolean eqModXRC(List<B> bs,T a,T b){
    if(a.equals(b)){ return true; }
    if(a instanceof T.X ax && b instanceof T.RCX br && br.x().name().equals(ax.name())){ return redundantOnX(bs,br.rc(),ax.name()); }
    if(a instanceof T.RCX ar && b instanceof T.X bx && ar.x().name().equals(bx.name())){ return redundantOnX(bs,ar.rc(),bx.name()); }
    if(!(a instanceof T.RCC aa && b instanceof T.RCC bb)){ return false; }
    if(aa.rc() != bb.rc() || !aa.c().name().equals(bb.c().name())){ return false; }
    var as= aa.c().ts(); var bs2= bb.c().ts();
    assert as.size() == bs2.size();
    return Streams.zip(as,bs2).allMatch((t1,t2)->eqModXRC(bs,t1,t2));
  }
  private boolean redundantOnX(List<B> bs,RC rc,String x){ return get(bs,x).rcs().equals(EnumSet.of(rc)); }  
}