package typeSystem;
import static core.RC.*;
import static offensiveUtils.Require.*;
import java.util.EnumSet;
import java.util.List;
import java.util.function.Function;

import core.*;
import core.E.*;
import message.TypeSystemErrors;
import utils.Streams;

public record Kinding(TypeSystemErrors tsE){
  public void checkC(E toErr, List<B> bs, T.C c){
    var d= decs().apply(c.name());
    var params = d.bs();
    var args= c.ts();
    assert eq(params.size(), args.size(), "Arity mismatch for " + c.name());
    Streams.zipI(args,params).forEach((i,arg,param)->check(toErr, c, i, bs, arg, param.rcs()));
  }
  public void check(E toErr, List<B> bs, T t){ 
    if (t instanceof T.RCC rcc){ check(toErr,rcc,-1,bs,rcc,EnumSet.allOf(RC.class)); }
  }
  public Function<TName,Literal> decs(){ return tsE.decs(); }
  public void check(E toErr, KindingTarget target, int index, List<B> bs, T t, EnumSet<RC> allowed){ switch(t){
    case T.RCC rcc -> checkRCC(toErr, target, index, bs, rcc, allowed);
    case T.RCX rcx -> checkRCX(toErr, target, index, rcx, allowed);
    case T.X x -> checkX(toErr, target, index, bs, x, allowed);
    case T.ReadImmX rix -> checkReadImmX(toErr, target, index, bs, rix, allowed);
  };}
  private void checkRCC(E toErr, KindingTarget target, int index, List<B> bs, T.RCC rcc, EnumSet<RC> allowed){
    if (!allowed.contains(rcc.rc())){ throw tsE.typeNotWellKinded(toErr,target,index,allowed); }
    checkC(toErr,bs,rcc.c());
  }
  private void checkRCX(E toErr, KindingTarget target, int index, T.RCX rcx, EnumSet<RC> allowed){
    if (!ofRCX(rcx,allowed)){ throw tsE.typeNotWellKinded(toErr,target,index,allowed); }
  }
  private void checkX(E toErr, KindingTarget target, int index, List<B> bs, T.X x, EnumSet<RC> allowed){
    if (!ofX(bs, x,allowed)){ throw tsE.typeNotWellKinded(toErr,target,index,allowed); }
  }
  private void checkReadImmX(E toErr, KindingTarget target, int index, List<B> bs, T.ReadImmX rix, EnumSet<RC> allowed){
    if (!ofReadImmX(bs,rix,allowed)){ throw tsE.typeNotWellKinded(toErr,target,index,allowed); }
  }
  public boolean of(List<B> bs, T t, EnumSet<RC> allowed){ return switch(t){
    case T.RCC rcc -> ofRCC(bs, rcc, allowed);
    case T.RCX rcx -> ofRCX(rcx, allowed);
    case T.X x -> ofX(bs, x, allowed);
    case T.ReadImmX rix -> ofReadImmX(bs, rix, allowed);
  };}
  private boolean ofRCC(List<B> bs, T.RCC rcc, EnumSet<RC> allowed){
    if (!allowed.contains(rcc.rc())){ return false; }
    var d= decs().apply(rcc.c().name());
    var params = d.bs();
    var args= rcc.c().ts();
    assert eq(params.size(), args.size(), "Arity mismatch for " + rcc.c().name());
    return Streams.zip(args,params).allMatch((arg,param)->of(bs, arg, param.rcs()));
  }
  private boolean ofRCX(T.RCX rcx, EnumSet<RC> allowed){
    return allowed.contains(rcx.rc());
  }
  private boolean ofX(List<B> bs, T.X x, EnumSet<RC> allowed){
    return allowed.containsAll(get(bs, x.name()).rcs());
  }
  private boolean ofReadImmX(List<B> bs, T.ReadImmX rix, EnumSet<RC> allowed){
    var rcs= get(bs, rix.x().name()).rcs();
    if (EnumSet.of(iso, imm).containsAll(rcs)){ return allowed.contains(imm); }
    if (EnumSet.of(mut, mutH, read, readH).containsAll(rcs)){ return allowed.contains(read); }
    return allowed.contains(imm) && allowed.contains(read);
  }
}