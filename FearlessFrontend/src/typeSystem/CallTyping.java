package typeSystem;

import java.util.List;
import java.util.ArrayList;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import core.*;
import core.E.*;
import inject.TypeRename;
import message.Reason;
import utils.Push;
import utils.Range;
import utils.Streams;
import typeSystem.TypeSystem.*;

record CallTyping(TypeSystem ts, List<B> bs, Gamma g, Call c, List<TRequirement> rs){
  List<Reason> run(){
    var rcc0= recvRcc();
    var d= ts.decs().apply(rcc0.c().name());
    assert d != null: rcc0.c().name();
    var sig= sigOf(d);
    checkTargsKinding(rcc0.c(),d,sig);
    var base= baseMType(rcc0.c(),d,sig);
    c.expectedRes().inner = base.t();
    var promos= ts.multiMeth(bs,base);
    var app= promos.stream().filter(m->rcc0.rc().isSubType(m.rc())).toList();
    if (app.isEmpty()){ throw ts.tsE().receiverRCBlocksCall(d,c,rcc0.rc(),promos); }
    var mat= typeArgsOnce(d,app);
    var possible= mat.candidatesOkForAllArgs();//This is indexes of MTypes allowed by the arguments
    if (possible.isEmpty()){ throw ts.tsE().methodPromotionsDisagreeOnArguments(c,mat); }
    if (rs.isEmpty()){ return List.of(Reason.pass(bestUnique(mat,possible))); }
    return rs.stream().map(req->resForReq(d,sig,mat,possible,req)).toList();
  }
  private T.RCC recvRcc(){
    var cts= new TypeSystem(ts.scope().pushCallRec(this.c),ts.v());
    var r= cts.typeOf(bs,g,c.e(),List.of());
    assert r.size() == 1;
    assert r.getFirst().isEmpty();//else would have thrown
    T t= r.getFirst().best;
    if (t instanceof T.RCC x){ return x; }
    throw ts.tsE().methodReceiverIsTypeParameter(cts.scope(),c,t);
  }
  private Sig sigOf(Literal d){
    var ms= d.ms().stream().map(M::sig)
      .filter(s->s.m().equals(c.name()) && s.rc() == c.rc()).toList();
    if (ms.isEmpty()){ throw ts.tsE().methodNotDeclared(ts.scope(),c,d); }
    assert ms.size() == 1 : "Duplicate cached sig for "+c.name()+" rc="+c.rc()+" in "+d.name();
    Sig sig= ms.getFirst();
    assert sig.ts().size() == c.es().size();//ensured by well formedness
    if (sig.bs().size() == c.targs().size()){ return sig; }
    throw ts.tsE().methodTArgsArityError(d,c,sig.bs());
  } 
  private MType baseMType(T.C c0, Literal d, Sig sig){
    var xs= Stream.concat(d.bs().stream(),sig.bs().stream()).map(B::x).toList();
    var ts0= Push.of(c0.ts(),c.targs());
    var ps= TypeRename.ofT(sig.ts(),xs,ts0);
    T ret= TypeRename.of(sig.ret(),xs,ts0);
    return new MType("As declared",sig.rc(),ps,ret);
  }
  private void checkTargsKinding(T.C c0, Literal d, Sig sig){
    assert c0.ts().size() == d.bs().size();
    var targs= c.targs();
    var kt= new KindingTarget.CallKinding(c0,c);
    Streams.zipI(targs,sig.bs()).forEach((i,targ,sigB)->ts.k().check(c,kt,i,bs,targ,sigB.rcs()));
  }
  private ArgMatrix typeArgsOnce(Literal d,List<MType> app){
    var size= c.es().size();
    var acc= new ArgMatrix(app,new ArrayList<>(size),new ArrayList<>(size));
    for (int argi : Range.of(0,size)){ accArgi(d,app,acc,c.es(), argi); }
    return acc;
  }
  private List<TRequirement> argRequirements(List<MType> app, int argi){
    //TODO:This is actually a really confusing point:
    //app has MTypes pre merged if two promotions had the same MType, but their argi may 
    //still be the same, so we are doing some duplicated computation when eventually do
    //the subtyping checks. The commented code below saves that duplicated computation
    //But if we deduplicate here we have to re expand directly later to be able to fit the
    //ArgMatrix acc with the right number of elements.
    return app.stream().map(m->new TRequirement(m.promotion(),m.ts().get(argi))).toList();
    /*var byT= new LinkedHashMap<T,List<String>>();
    for (var m:app){
      var t= m.ts().get(argi);
      byT.computeIfAbsent(t,_->new ArrayList<>()).add(m.promotion());
    }
    return byT.entrySet().stream()
      .map(e->new TRequirement(
        Join.of(e.getValue().stream().distinct(),"",", ",""),
        e.getKey()))
      .toList();*/
  }
  private void accArgi(Literal d, List<MType> app, ArgMatrix acc, List<E> es, int argi){
    var reqs= argRequirements(app,argi);
    var cts= new TypeSystem(ts.scope().pushCallArgi(this.c, argi),ts.v());
    var res= cts.typeOf(bs,g,es.get(argi),reqs);
    assert res.size() == app.size(): res.size()+" "+app.size();
    var ok= okSet(res);
    if (ok.isEmpty()){
      throw cts.tsE().methodArgumentCannotMeetAnyPromotion(cts,bs,d,c,argi,reqs,res);
    }
    acc.okByArg().add(ok);
    acc.resByArg().add(res);
  }
  private static List<Integer> okSet(List<Reason> res){
    return IntStream.range(0,res.size()).filter(i->res.get(i).isEmpty()).boxed().toList();
  }
  private Reason resForReq(Literal d, Sig sig, ArgMatrix mat, List<Integer> possible, TRequirement req){
    List<Integer> okRet= possible.stream()
      .filter(i->ts.isSub(bs,mat.candidate(i).t(),req.t())).toList();
    if (!okRet.isEmpty()){ return Reason.pass(bestUnique(mat,okRet)); }
    return Reason.callResultCannotHaveRequiredType(ts,d,c, bs, mat, possible, req, bests(mat,possible),sig,ts.scope());
  } 
  //Unique unless the minimal types are a bare 'X' and some 'rc X'. A bare X stands for its whole
  //bound, so those two are incomparable, but both are sound and the "As declared" one comes first.
  private T bestUnique(ArgMatrix mat, List<Integer> idxs){ return bests(mat,idxs).getFirst(); }
  private List<T> bests(ArgMatrix mat, List<Integer> idxs){
    List<T> all= idxs.stream().map(i->mat.candidate(i).t()).toList();
    return all.stream()
      .filter(ti->all.stream().noneMatch(tj->
        !tj.equals(ti) && ts.isSub(bs,tj,ti)))
      .distinct().toList();
  }
}