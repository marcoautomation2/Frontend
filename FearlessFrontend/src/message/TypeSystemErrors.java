package message;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.IntStream;

import fearlessParser.Parser;
import inject.TypeRename;
import metaParser.NameSuggester;
import typeSystem.TypeSystem.*;
import typeSystem.ArgMatrix;
import typeSystem.Change;
import typeSystem.TypeScope;
import typeSystem.TypeSystem;
import utils.Join;
import utils.OneOr;
import utils.Range;
import utils.Streams;
import core.*;
import core.E.*;

import static message.Err.*;

public record TypeSystemErrors(Function<TName,Literal> decs, pkgmerge.Package pkg, Map<String,String> map){
  public Err err(){
   Function<TName,TName> f= n->{
     var res= decs.apply(n);
     if (res == null){ return n; }
     if (!res.infName() || res.cs().isEmpty()){ return n; }
     return res.cs().getFirst().name();
   };
   Function<T.C,T.C> publicHead= c->{
     var d= decs.apply(c.name());
     if (!d.infName()){ return c; }
     var xs= d.bs().stream().map(B::x).toList();
     return d.cs().stream()
       .<T.C>map(sc->TypeRename.of(sc, xs, c.ts()))
       .filter(scC->!decs.apply(scC.name()).infName())
       .findFirst().orElseThrow();
    };
   return new Err(publicHead,f,t->new CompactPrinter(pkg().name(),map,t),new StringBuilder()); }
  public FearlessException baseIdBadBody(Literal l, M m){
    String x= m.xs().getFirst();
    return err()
      .line(up(err().expRepr(l))+" implements "+err().tNameADisp(LiteralDeclarations.baseId)+".")
      .line("The body of "+err().methodSig(m.sig().m())+" must be "+disp(x)+" or "+disp(x+".as{...}")+".")
      .line("Only those two shapes are the identity function.")
      .ex(m.e().get()).addSpan(m.e().get().span().inner);
  }
  public FearlessException mCallFrame(M m, FearlessException fe){
    return fe.addFrame(err().methodSig(m.sig().m())+" line "+m.sig().span().inner.startLine(), m.sig().span().inner);
  }
  private FearlessException withCallSpans(FearlessException ex, Call c){
    return ex.addSpan(Parser.span(c.pos(), c.name().s().length())).addSpan(c.span().inner);
  }
  private FearlessException addExpFrame(E toErr,FearlessException err){
    return err.addFrame(err().expRepr(toErr),toErr.span().inner);
  }
  private FearlessException overrideErr(Literal l, Sig sub, Err e){
    return addExpFrame(l, e.ex(l).addSpan(sub.span().inner));
  }
  ///Fired when a generic instantiation Id[Ts] does not respect the RC bounds
  ///declared in Id[Bs]. This is a "type arguments vs generic header" error,
  ///not a method-resolution or expression-typing error.
  ///Raised when checking types anywhere they appear.
  public FearlessException typeNotWellKinded(E toErr, KindingTarget target, int index, EnumSet<RC> bounds){
    assert index >= 0;
    String allowedStr= Join.of(bounds.stream().map(Err::disp).sorted(), "", " or ", "");
    Err err= switch(target){
      case T.RCC rcc -> typeNotWellKinded("type "+err().typeRepr(true,rcc),rcc.c(), index, allowedStr);
      case T.C c -> typeNotWellKinded("type "+err().typeRepr(c),c, index, allowedStr);
      case KindingTarget.CallKinding(var t,var c)   -> typeNotWellKindedSig(t,c, index, allowedStr);
    };
    var span= toErr.span().inner.contained(target.span().inner) ? target.span().inner : toErr.span().inner;
    return addExpFrame(toErr,err.ex(toErr).addSpan(span));
  }
  private Err typeNotWellKinded(String name,T.C c, int index, String allowedStr){
    var args= c.ts();
    assert index >= 0 && index < args.size();
    T bad= args.get(index);
    var bs= decs.apply(c.name()).bs();
    assert index < bs.size();
    String typeName = err().tNameADisp(c.name());
    String paramName= disp(bs.get(index).x());
    return err().pTypeArgBounds(name, typeName, paramName, index, err().typeRepr(true,bad), allowedStr);
  }
  private Err typeNotWellKindedSig(T.C t, E.Call c, int index, String allowedStr){
    var ms= decs.apply(t.name()).ms();
    var m= OneOr.of("Malformed methods",ms.stream().filter(mi->mi.sig().m().equals(c.name()) && mi.sig().rc() == c.rc()));
    var bs= m.sig().bs();
    assert index >= 0 && index < bs.size();
    var param= bs.get(index);
    String decName   = err().methodSig(c.rc().toStrSpace(),t.name(), c.name()); // p.A.m(...)
    T bad            = c.targs().get(index);
    return err().pTypeArgBounds("call to "+err().methodSig(c.name()), decName, disp(param.x()), index, err().typeRepr(true,bad), allowedStr);
  } 
  ///Overriding method in literal l is not a valid subtype of inherited method.
  ///Raised when checking object literals
  public FearlessException methodOverrideSignatureMismatchContravariance(TypeSystem ts, List<B> ctx, Literal l, Sig current, Sig parent, int index){
    var mName= current.m();
    assert mName.equals(parent.m());  
    assert index >= 0 && index < current.ts().size() && index < parent.ts().size();
    T parentArg= parent.ts().get(index);
    T currentArg= current.ts().get(index);
    assert !ts.isSub(ctx, parentArg, currentArg);
    String inverse= ts.isSub(ctx, currentArg, parentArg)
      ? "It is instead a supertype: you are strengthening the parameter instead of weakening it."
      : "The two types are unrelated.";
    return overrideErr(l, current, err()
      .invalidMethImpl(current.rc().toStrSpace(),l,mName)
      .line("The method "+err().methodSig(mName)+" accepts parameter "+(index+1)+" of type "+err().typeRepr(true,currentArg)+".")
      .line("But "+err().methodSig(current.rc().toStrSpace(),parent.origin(),mName)+" requires "+err().typeRepr(true,parentArg)+", which is not a subtype of "+err().typeRepr(true,currentArg)+".")
      .line(inverse)
    );
  }
  ///Overriding method in literal l is not a valid subtype of inherited method.
  ///Raised when checking object literals
  public FearlessException methodOverrideSignatureMismatchCovariance(TypeSystem ts, List<B> ctx, Literal l, Sig current, Sig parent){
    var mName=current.m();
    assert mName.equals(parent.m());
    T parentRet= parent.ret();
    T currentRet= current.ret();
    assert !ts.isSub(ctx, currentRet, parentRet);
    String inverse= ts.isSub(ctx, parentRet, currentRet)
      ? "It is instead a subtype: you are weakening the result instead of strengthening it."
      : "The two types are unrelated.";
    return overrideErr(l, current, err()
      .invalidMethImpl(current.rc().toStrSpace(),l,mName)
      .line("The method "+err().methodSig(mName)+" returns type "+err().typeRepr(true,currentRet)+".")
      .line("But "+err().methodSig(current.rc().toStrSpace(),parent.origin(),mName)+" returns type "+err().typeRepr(true,parentRet)+", which is not a supertype of "+err().typeRepr(true,currentRet)+".")
      .line(inverse)
    );
  }
  ///A required method was left abstract instead of being implemented.
  ///Raised when checking object literals
  public FearlessException callableMethodStillAbstract(E at, M got, Literal l){
    var s= got.sig();
    return addExpFrame(at, err()
      .line("This object literal is missing a required method.")
      .line("Missing: "+err().methodSig(s.rc()+" ", s.m())+".")
      .line("Required by: "+err().tNameADisp(s.origin())+".")
      .line("Hint: add an implementation for "+err().methodSig(s.m())+" inside the object literal.")
      .ex(at));
  }
  public FearlessException typeDeclaredInMethod(E at, Literal l){
    return addExpFrame(at, err()
      .line("The type "+err().tNameADisp(l.name())+" is declared inside a method body.")
      .line("A type declared inside a method can capture any parameter name in scope,")
      .line("so it cannot be extended or instantiated.")
      .line("Hint: if it captures nothing, declare it implementing \"base.CaptureFree\".")
      .ex(at));
  }
  ///Implemented method can never be called for any receiver obtained from the literal.
  ///Its body is statically dead code (typically a mut method on an imm/read literal).
  ///Raised when checking object literals   
  public FearlessException methodImplementationDeadCode(TSpan at, M got, Literal l){
    var s= got.sig();
    assert s.rc() == RC.mut;
    assert l.rc() == RC.imm || l.rc() == RC.read;
    String m= err().methodSig(s.rc()+" ", s.m());
    return addExpFrame(l, err()
      .line("The method "+err().methodSig(s.rc().toStrSpace(),l,s.m())+" is dead code.")
      .line("The "+err().expRepr(l.withRC(RC.imm))+" is "+disp(l.rc())+", so it will never be seen as "+disp(RC.mut)+".")
      .line("But it implements method "+m+", which requires a "+disp(RC.mut)+" receiver.")
      .ex(l).addSpan(at.inner));
  }  
  ///Iso parameter is used in a way that violates affine discipline.
  ///Allowed uses: capture into object literals as imm, or use directly at most once.
  ///if !earlyErrOnMoreThenOnceDirectly then used exactly once directly but ALSO used in literals
  ///Raised when checking object literals
  public FearlessException notAffineIso(Literal l,M m, String name, boolean earlyErrOnMoreThenOnceDirectly, List<E.X> usages){
    assert !usages.isEmpty();
    int line= m.sig().span().inner.startLine();
    String ms= err().methodSig(m.sig().rc().toStrSpace(),l, m.sig().m());
    String x= disp(name);
    var e= err()
      .line("Iso parameter "+x+" violates the single-use rule in method "+ms+" (line "+line+").");
    if (earlyErrOnMoreThenOnceDirectly){
      e.line("It is used directly "+usages.size()+" times.");
      e.line("Iso parameters can be used directly at most once.");
    } 
    else{
      e.line("It is used directly and also captured into object literals.");
      e.line("An iso parameter must be either captured, or used directly once (but not both).");
    }
    e.line("Allowed: capture into object literals as "+disp(RC.imm)+", or use directly once.");
    var ex= e.ex(m.e().get());
    for (var u:usages){ ex.addSpan(u.span().inner); }
    return ex;
  }
  ///Expression at method body has a type that does not meet its result requirement(s).
  ///"body has wrong type" error; can only trigger if all current-expressions at are well typed.
  ///Raised when checking object literals
  public FearlessException methBodyWrongType(TypeScope.Method s, E at, Reason got, T req){
    Literal l= s.l();
    M m= s.m();
    assert !got.isEmpty();
    var got0= err().typeRepr(true,got.best);
    var req0= err().typeRepr(true,req);
    var e= err();
    String meth= err().methodSig(m.sig().m());
    var top= l.thisName().equals("this");
    if (top){ e.line("The body of method "+meth+" of "+err().expRepr(l)+" is an expression returning "+got0+"."); }
    else{ e.line("Method "+meth+" inside the "+err().expRepr(l) + " (line "+l.span().inner.startLine()+")"
      +"\nis implemented with an expression returning "+got0+"."); }
    e.line(up(got.info));
    E ctx= got.footerE.get();
    FearlessException ex= e.exInferMsg(ctx,req0);
    return addExpFrame(at, ex.addSpan(at.span().inner));
  }
  ///Parameter x is syntactically in scope but its value was dropped by viewpoint adaptation.
  ///Raised when a use of x occurs after capturing have made it unavailable.
  ///Raised when checking parameters.
  public FearlessException parameterNotAvailableHere(E.X x, T declared, Change.NoT why, List<B> bs){
    return addExpFrame(x,err()
      .line(whyDrop(err().expRepr(x),why))
      .ex(x)
      .addSpan(x.span().inner));
  }
  private String whyDrop(String subject, Change.NoT why){
    return why.<Supplier<String>>name(
      ()->whyDropMutInImm(subject,why),
      ()->whyDropReadHMutH(subject,why),
      ()->whyDropFTV(subject,why),
      ()->whyDropCapFree(subject,why)
      ).get();
  }
  private String whyDropMutInImm(String subject, Change.NoT why){
    return subject+" has type "+err().typeRepr(true,why.atDrop())+".\n"
    + subject+" can observe mutation; thus it cannot be captured in the "+disp(why.l().rc())+" "+err().expRepr(why.l())
    +" (line "+why.l().span().inner.startLine()+").\n"
    +"Hint: capture an immutable copy instead, or move this use outside the object literal.";
  }
  private String whyDropReadHMutH(String subject, Change.NoT why){
    String explicitH= why.atDrop().explicitH()
      ? "The type of "+subject+" is hygienic (readH or mutH)\n"
      : "The type of "+subject+" can be instantiated with hygienics (readH or mutH)\n";
    return subject+" has type "+err().typeRepr(true,why.atDrop())+".\n"
    + explicitH+ "and thus it cannot be captured in the "+err().expRepr(why.l())
    +" (line "+why.l().span().inner.startLine()+").\n";
  }
  private static String hintAddTypeParameter(Change.NoT why){
    var name= why.l().name().simpleName();
    var current= disp(Join.of(why.l().bs().stream().map(B::x),name+"[",",","]",name));
    var next= disp(Join.of(why.l().bs().stream().map(B::x),name+"[",",",",...]",name+"[...,...]"));
    return"Hint: change "+current+" by adding the missing type parameters: "+next;
  }
  private String whyDropFTV(String subject, Change.NoT why){
    return subject+" has type "+err().typeRepr(true,why.atDrop())+".\n"
    + subject+" uses type parameters that are not propagated\n"
    + "into "+err().expRepr(why.l())
    +" (line "+why.l().span().inner.startLine()+")"
    + " and thus it cannot be captured.\n"
    + hintAddTypeParameter(why);
  }
  private String whyDropCapFree(String subject, Change.NoT why){
    return 
    err().expRepr(why.l())+" implements \"base.CaptureFree\".\n"
    + "Thus "+subject
    +" (line "+why.l().span().inner.startLine()+")"
    + " cannot be captured in this scope.\n";
  }  
  ///Receiver expression of call c is typed into a type parameter (X / RC X / read/imm X), not a concrete RC C.
  ///Methods cannot be called on type parameters, so this call can never resolve.
  ///Raised when checking method calls.
  public FearlessException methodReceiverIsTypeParameter(TypeScope s,Call c, T recvType){
    var best= TypeScope.bestInterestingScope(s, List.of(recvType));
    return withCallSpans(err()
      .pCallCantBeSatisfied(c)
      .line("The receiver is of type "+err().typeRepr(true,recvType)+". This is a type parameter.")
      .line("Type parameters cannot be receivers of method calls.")
      .exInferMsg(best.contextE(),err().typeRepr(true,recvType)),c);
  }
  ///No method matches call c.
  ///Sub-errors for more clarity
  /// - no such name at all; searching for similar names with "Did you mean..."
  /// - method name exist but with different arity; error will list those other method signatures
  /// - method exists with right arity, but different receiver RCs; list those other method signatures
  ///Raised when checking method calls.
  public FearlessException methodNotDeclared(TypeScope scope, Call c, Literal d){
    Literal di= d.withRC(RC.imm);
    String _on= err().onTypeOrAnon(di);
    String subj= err().theTypeOrObjectLiteral(di);
    String on= c.e().equals(d) ? _on : subj;
    Err e= err()
      .pCallCantBeSatisfied(c)
      .line("Method "+err().methodSig(c.name())+" is not declared on "+on+".");
    String name= c.name().s();
    var candidates= d.ms().stream().map(M::sig).toList();
    List<Sig> sameName= candidates.stream()
      .filter(s->s.m().s().equals(name)).toList();
    if (sameName.isEmpty()){
      addEnclosingLiteralHintIfReceiverIsThis(e,scope,c,name,subj);
      if (candidates.isEmpty()){ e.line(up(subj)+" does not have any methods."); }
      else{
        var names= candidates.stream().map(s->s.m().s()).distinct().sorted().toList();
        NameSuggester.suggest(name, names,(_,cs,best)->{ bestNameMsg(e,on,c, d, candidates, cs, best); return null; } );
      }
      return withCallSpans(e.ex(c), c);
    }
    var sameArity= sameName.stream().filter(s->s.m().arity() == c.es().size()).toList();
    if (sameArity.isEmpty()){
      String avail= Join.of(sameName.stream().map(s->Integer.toString(s.m().arity())).distinct().sorted(), "", " or ", "");
      return withCallSpans(err()
        .pCallCantBeSatisfied(c) 
        .line("There is a method "+disp(c.name().s())+" on "+on+",\nbut with different number of arguments.")
        .line("This call supplies "+c.es().size()+", but available methods take "+avail+".")
        .ex(c), c);
    }
    String availRc= Join.of(sameArity.stream().sorted().map(s->disp(s.rc())), "", " and ", ".");
    return withCallSpans(err()
      .pCallCantBeSatisfied(c)
      .line(err().methodSig(c.name())+" exists on type "+err().bestNameNoRc(d)+", but not with the requested capability.")
      .line("This call requires the existence of a "+disp(c.rc())+" method.")
      .line("Available capabilities for this method: "+availRc)
      .ex(c), c);
  }
  private void addEnclosingLiteralHintIfReceiverIsThis(Err e, TypeScope scope, Call c, String name, String on){
    if (!(c.e() instanceof X x && x.name().equals("this"))){ return; }
    for (var s= scope; !s.isTop(); s= s.outer()){
      if (!(s instanceof TypeScope.Method meth)){ continue; }
      Literal l= meth.l();
      boolean has= l.ms().stream().anyMatch(m->m.sig().m().s().equals(name));
      if (!has){ continue; }
      String sig= err().methodSig(c.name());
      String type= err().tNameADisp(l.name());
      String selfName= l.thisName();
      e.line("Hint:")
       .line("The method parameter \"this\" here has "+on+".")
       .blank();
      if (selfName.equals("_")){
        e.line("The method "+sig+" is defined in the object literal of type "+type+".")
         .line("No parameter refers to instances of this literal.")
         .line("To declare one, use the single quote as in the example below:")
         .line("  Rectangles: { #(width: Nat, height: Nat): Rectangle -> Rectangle:{'rect")
         .line("    .area: Nat -> width * height;")
         .line("    .str: Str -> \"area: \"+(rect.area.str);")
         .line("    .withWidth(width': Nat): Rectangle -> this#(width', height);")
         .line("  }}");
      }else{
        e.line("The method "+sig+" is defined in the object literal of type "+type+"; the parameter "
             + "referring to its instances is named "+disp(selfName)+".");
      }
      return;
    }
  }
  void bestNameMsg(Err e, String onStr, Call c, Literal d, List<Sig> candidates, List<String> cs, Optional<String> best){
    best.ifPresent(b->e.line("Did you mean "+disp(b)+" ?"));
    e.blank().line("Available methods on "+onStr+":");
    for (String n:cs){
      candidates.stream()
        .filter(s->s.m().s().equals(n))
        .forEach(s->e.bullet(e.cp().sig(s)));
    }
  }
  ///A method matching c by name / arity / RC exists, but c supplies the wrong number of type arguments.
  ///Triggered only for explicitly written [Ts]; inference never reaches this error.
  ///Raised when checking method calls.
  public FearlessException methodTArgsArityError(Literal d, Call c, List<B> bs){
    int expected= bs.size();
    String args= Join.of(bs.stream().map(b->disp(b.x())), ": ", " and ","","");
    int got= c.targs().size(); assert got != expected;
    String expS= expected == 0 
      ? "no type arguments" 
      : expected+" type argument"+(expected == 1 ? args : "s"+args);
    String gotS= got == 0 
      ? "no type arguments" 
      : got+" type argument"+(got == 1 ? "" : "s");
    return withCallSpans(err()
      .pCallCantBeSatisfied(d,c)
      .line("Wrong number of type arguments for "+err().methodSig(c.name())+".")
      .line("This method expects "+expS+"; but this call provides "+gotS+".")
      .ex(c), c);
  }
  ///Methods exist for call c, but the receiver capability is too weak for all the available promotions.
  ///No promotion accepts this receiver, so the call cannot succeed regardless of argument types.
  ///Raised when checking method calls.
  public FearlessException receiverRCBlocksCall(Literal d, Call c, RC recvRc, List<MType> promos){
    List<String> needed= promos.stream().map(MType::rc).distinct().sorted().map(Err::disp).toList();
    return withCallSpans(err()
      .pCallCantBeSatisfied(d,c)
      .line("The receiver (the expression before the method name) has capability "+disp(recvRc)+".")
      .line(Join.of(needed,"This call requires a receiver with capability "," or ","."))
      .pReceiverRequiredByPromotion(promos)
      .ex(c), c);
  }
  ///For argument index argi in call c, the argument's type does not satisfy any promotion's requirement.
  ///Receiver and arguments are well typed, but this argument does not match any promotion.
  ///Sub-errors for more clarity
  /// - The argument type has the wrong nominal type, Person vs Car. In this case, promotions are not mentioned, just the general type mismatch.
  ///   This should also suppress detail from parameter Reason object
  /// - The argument best type met the intended nominal type, but the RC is off.
  ///   Here the Reason object should help to provide clarifications
  /// - Arguments return type is likely impacted by inference: argument is a generic method call or object literal
  ///   Do the Reason help here? if not, can we expand it or provide a parallel support?
  ///Raised when checking method calls.
  public FearlessException methodArgumentCannotMeetAnyPromotion(TypeSystem ts,List<B> bs, Literal d, Call c, int argi, List<TRequirement> reqs, List<Reason> res){
    assert argi >= 0 && argi < c.es().size();
    assert !reqs.isEmpty();
    assert reqs.size() == res.size();
    assert res.stream().noneMatch(r->r.isEmpty());
    T reqCanon= reqCanon(reqs);
    if (isWrongUnderlyingType(ts,bs,reqCanon,res)){ return wrongUnderlyingTypeErr(ts,d,c,argi,reqs,res); }
    T gotHdr= headerBest(res);
    var any= reqs.stream().map(TRequirement::t).map(t->err().typeRepr(false,t)).distinct().toList();
    var r= pickReason(reqs,res);
    var e= err()
      .pCallCantBeSatisfied(d,c)
      .line("Argument "+(argi+1)+" has type "+err().typeRepr(true,gotHdr)+".")
      .notInSubtypeList(any)
      .line(up(r.info))
      .blank()
      .line("Type required by each promotion:");
    var byT= new LinkedHashMap<T,List<String>>();
    for (var ri:reqs){ byT
      .computeIfAbsent(ri.t(),_->new ArrayList<>())
      .add(ri.reqName());
    }
    for (var ent:byT.entrySet()){
      var names= ent.getValue().stream().distinct().toList();
      e.bullet(err().typeRepr(false,ent.getKey())+"  ("+Join.of(names,"",", ","")+")");
    }
    addNoPrecedenceHintIfOperator(e,c);
    var footer= r.footerE.get();
    return withCallSpans(e.exInferMsg(footer,err().typeRepr(false,reqs.getFirst().t())),c);
  }
  private FearlessException wrongUnderlyingTypeErr(TypeSystem ts, Literal d, Call c, int argi, List<TRequirement> reqs, List<Reason> res){
    T gotHdr= headerBest(res);//TODO: Eventually this will need to be matched with the meth body subtype and both
    T required= reqs.getFirst().t(); //should make an attempt to say what the generics in the result should have been instantiate to instead
    //in particular here we are in a methCall, so we can talk about OUR type args impacting the expected argument type
    //TODO: line reqs.getFirst().t(); above, should we use the best return with ordering on rcs?
    var e= err()
      .pCallCantBeSatisfied(d,c)
      .line("Argument "+(argi+1)+" has type "+err().typeRepr(true,gotHdr)+".")
      .line("That is not a subtype of "+err().typeRepr(true,required)+" (the type required by the method signature).");
    addNoPrecedenceHintIfOperator(e,c);
    return withCallSpans(e.ex(ts.scope().pushCallArgi(c,argi).contextE()), c);
  }
  private void addNoPrecedenceHintIfOperator(Err e, Call c){
    String s= c.name().s();
    if (s.startsWith(".") || s.equals("#")){ return; }
    e.line("Hint: Fearless has no operator precedence, so an expression like \"a.get + b.get\" "
         + "parses as \"(a.get + b).get\", not \"a.get + (b.get)\". "
         + "If this argument needed a method applied to it first, wrap it in parentheses.");
  }
  private static T reqCanon(List<TRequirement> reqs){
    T c0= canon(reqs.getFirst().t());
    assert reqs.stream().allMatch(r->canon(r.t()).equals(c0));
    return c0;
  }
  private static boolean isWrongUnderlyingType(TypeSystem ts, List<B> bs, T reqCanon, List<Reason> res){
    return res.stream().map(r->canon(r.best)).noneMatch(r->ts.isSub(bs, r, reqCanon));
  }
  private static T canon(T t){ return t.withRC(core.RC.imm); }

  private static T headerBest(List<Reason> res){
    return res.stream().map(r->r.best)
      .min(Comparator.comparingInt(TypeSystemErrors::headerKey))
      .orElseThrow();
  }
  private static int headerKey(T t){ return switch(t){
    case T.RCC r -> r.rc().ordinal();
    case T.RCX r -> r.rc().ordinal();
    case T.X _ -> 1000;
    case T.ReadImmX _ -> 1001;
  };}
  private static Reason pickReason(List<TRequirement> reqs, List<Reason> res){
    return res.get(Streams.firstPos(res, i->rcOnlyMismatch(res.get(i).best, reqs.get(i).t())).orElse(0));
  }
  ///Each argument of call c is compatible with at least one promotion, but no promotion fits all arguments.
  ///The per-argument sets of acceptable promotions have empty intersection.
  ///Raised when checking method calls.
  ///Error details
  ///  - What arguments satisfy what promotion and why (best type <: required type1, required type 2 etc)  
  public FearlessException methodPromotionsDisagreeOnArguments(Call c, ArgMatrix mat){
    int args= mat.okByArg().size();
    assert args > 0 && mat.resByArg().size() == args;
    var e= err()
      .pCallCantBeSatisfied(c)
      .line("Each argument is compatible with at least one promotion, but no single promotion fits all arguments.")
      .blank()
      .line("Compatible promotions by argument:");
    for (int argi : Range.of(0,args)){
      var ok= mat.okByArg().get(argi);
      assert !ok.isEmpty();
      var promos= ok.stream().map(i->mat.candidate(i).promotion()).distinct().sorted().toList();
      var got= err().typeRepr(true,headerBest(mat.resByArg().get(argi)));
      e.bullet("Argument "+(argi+1)+" has type "+got+" and is compatible with: "+Join.of(promos,"",", ","")+".");
    }
    e.blank().pPromotionFailuresHdr();
    var byArg= IntStream.range(0,args)
      .mapToObj(_->new LinkedHashMap<String,List<String>>()).toList();
    int promosN= mat.resByArg().getFirst().size();
    for (int pi : Range.of(0,promosN)){
      int argi= firstFailingArg(mat, pi);
      Reason r= mat.resByArg().get(argi).get(pi);
      assert !r.isEmpty();
      byArg.get(argi).computeIfAbsent(up(r.info),_->new ArrayList<>())
        .add(mat.candidate(pi).promotion());
    }
    for (int argi : Range.of(0,args)){
      for (var ent: byArg.get(argi).entrySet()){
        var names= ent.getValue();
        e.pPromoFailure(
          "Argument "+(argi+1)+Join.of(names," fails:    ",", ","\n")+ent.getKey()
        );
      }
    }
  return withCallSpans(e.ex(c), c);
  }
  private static int firstFailingArg(ArgMatrix mat, int promoIdx){
    return Streams.firstPos(mat.okByArg(), argi->!mat.okByArg().get(argi).contains(promoIdx)).get();
  }
}