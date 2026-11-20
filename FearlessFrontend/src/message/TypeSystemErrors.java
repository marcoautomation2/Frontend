package message;

import static message.Err.*;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import inject.TypeRename;
import metaParser.NameSuggester;
import pkgmerge.Package;
import typeSystem.TypeSystem.*;
import typeSystem.ArgMatrix;
import typeSystem.Change;
import typeSystem.Gamma;
import typeSystem.TypeScope;
import typeSystem.TypeSystem;
import utils.Bug;
import utils.Join;
import utils.OneOr;
import utils.Range;
import utils.Streams;
import core.*;
import core.E.*;

public record TypeSystemErrors(Function<TName,Literal> decs, Package pkg, LinkedHashSet<String> printed){
  public Err err(){ return new WellFormednessErrors(pkg.name(), pkg.map(), pkg.mapSources(), printed).err(this::publicHead, this::preferredForFresh, decs, List.of()); }
  private TName preferredForFresh(TName n){
    var res= decs.apply(n);
    var showSuper= res.infName() && !res.cs().isEmpty();
    if (!showSuper){ return n; }
    return res.cs().getFirst().name();
  }
  private T.C publicHead(T.C c){
    var d= decs.apply(c.name());
    if (!d.infName()){ return c; }
    return d.cs().stream()
      .map(sc -> sc.withTs(TypeRename.ofT(sc.ts(), B.xs(d.bs()), c.ts())))
      .filter(scC -> !decs.apply(scC.name()).infName())
      .findFirst().orElse(c);
  }
  public FearlessException baseIdBadBody(Literal l, M m){
    var x= m.xs().getFirst();
    var e= err().line(up(err().expRepr(l))+" implements "+err().tNameADisp(LiteralDeclarations.baseId)+".");
    var span= m.e().get().span().inner;
    var asOnX= m.e().get() instanceof Call c && c.e() instanceof X(var recv, _) && recv.equals(x) && c.name().equals(new MName(".as", 1));
    if (!asOnX){ return e
      .line("The body of "+err().methodSig(m.sig().m())+" must be "+disp(x)+" or "+disp(x+".as{...}")+".")
      .line("Only those two shapes are the identity function.")
      .typeErr().addSpan(span);
    }
    return e
      .line("The body of "+err().methodSig(m.sig().m())+" calls "+err().methodSig(new MName(".as", 1))+" on parameter "+disp(x)+".")
      .line("Calling "+err().methodSig(new MName(".as", 1))+" counts as the identity function only when the receiver has a type implementing "+err().tNameADisp(LiteralDeclarations.baseContainer)+".")
      .line("Parameter "+disp(x)+" has type "+err().typeRepr(true, m.sig().ts().getFirst())+".")
      .typeErr().addSpan(span);
  }
  private static Optional<fearlessFullGrammar.M> srcM(Literal l, Sig s){
    List<fearlessFullGrammar.M> ms= switch (l.src().inner){
      case fearlessFullGrammar.Declaration d -> d.l().methods();
      case fearlessFullGrammar.E.Literal gl -> gl.methods();
      case fearlessFullGrammar.E.TypedLiteral t -> t.l().map(fearlessFullGrammar.E.Literal::methods).orElse(List.of());
      default -> throw Bug.unreachable();
    };
    return OneOr.opt("Malformed methods", ms.stream().filter(mi -> mi.span().inner.equals(s.span().inner)));
  }
  private static boolean wholeSig(fearlessFullGrammar.M fm, Sig s){
    return !fm.hasImplicit() && fm.sig().filter(gs -> (gs.rc().isPresent() || s.rc() == RC.imm) && gs.t().isPresent() && gs.parameters().stream().allMatch(p -> p.t().isPresent())).isPresent();
  }
  private Optional<T.C> parent(Literal l, Sig s){ return l.cs().stream().filter(c -> declared(c, s).isPresent()).findFirst(); }
  private String parentSig(T.C c, Sig s){ return methodSig(err().cp().msgT(new T.RCC(RC.imm, c, c.span())), s.m()); }
  private Optional<String> inheritedSig(Literal l, M m){
    var fm= srcM(l, m.sig());
    var parent= parent(l, m.sig());
    if (fm.isEmpty() || wholeSig(fm.get(), m.sig()) || parent.isEmpty()){ return Optional.empty(); }
    return Optional.of("Method "+err().methodSig(m.sig().m())+" inherited the signature from "+parentSig(parent.get(), m.sig())+" as follows:\n"+err().cp().sig(m));
  }
  private Optional<String> renamedGenerics(Literal l, M m){
    var fm= srcM(l, m.sig());
    var parent= parent(l, m.sig());
    var written= fm.flatMap(fearlessFullGrammar.M::sig).flatMap(fearlessFullGrammar.Sig::bs).isPresent();
    if (fm.isEmpty() || written || parent.isEmpty()){ return Optional.empty(); }
    return renamed(parentSig(parent.get(), m.sig()), declared(parent.get(), m.sig()).get().bs(), m.sig().bs(), _ -> true);
  }
  private Optional<Sig> declared(T.C c, Sig s){
    return decs.apply(c.name()).ms().stream().map(M::sig).filter(ps -> ps.origin().equals(c.name()) && ps.m().equals(s.m()) && ps.rc() == s.rc()).findFirst();
  }
  public FearlessException mCallFrame(Literal l, M m, FearlessException fe){
    return fe.addFrame("method "+err().methodSig("", l, m.sig().m())+" (line "+m.sig().span().inner.startLine()+")", m.sig().span().inner);
  }
  private FearlessException withCallSpans(FearlessException ex, Call c){
    return ex.addSpan(TSpan.fromPos(c.pos(), c.name().s().length()).inner).addSpan(c.span().inner);
  }
  private FearlessException withCallSpans(FearlessException ex, E at, Call c){
    if (!at.span().inner.isSingleLine()){ return withCallSpans(ex, c); }
    return ex.addSpan(at.span().inner).addSpan(c.span().inner);
  }
  private FearlessException addExpFrame(E toErr, FearlessException err){
    return err.addFrame(err().expRepr(toErr), toErr.span().inner);
  }
  private FearlessException overrideErr(Literal l, Sig current, Sig parent, String got, String want, String why){
    var e= err()
      .line("Invalid method signature for "+err().methodSig(current.rc().toStrSpace(), l, current.m())+".")
      .line("The method "+err().methodSig(current.m())+" "+got+".")
      .line("But "+err().methodSig(current.rc().toStrSpace(), parent.origin(), current.m())+" "+want+".")
      .line(why);
    return addExpFrame(l, e.ex(l).addSpan(current.span().inner));
  }
  ///Fired when a generic instantiation Id[Ts] does not respect the RC bounds
  ///declared in Id[Bs]. This is a "type arguments vs generic header" error,
  ///not a method-resolution or expression-typing error.
  ///Raised when checking types anywhere they appear.
  public FearlessException typeNotWellKinded(E toErr, KindingTarget target, int index, EnumSet<RC> bounds, EnumSet<RC> got){
    assert index >= 0;
    var err= switch (target){
      case T.C c -> typeNotWellKinded("The type "+err().typeRepr(c)+" is invalid.", c, index, caps(bounds), caps(got));
      case KindingTarget.CallKinding(var t, var c) -> typeNotWellKindedSig(t, c, index, caps(bounds), caps(got));
    };
    var span= toErr.span().inner.contained(target.span().inner) ? target.span().inner : toErr.span().inner;
    return addExpFrame(toErr, err.ex(toErr).addSpan(span));
  }
  private static String caps(EnumSet<RC> rcs){ return (rcs.size() == 1 ? "capability " : "capabilities ")+Join.of(rcs.stream().map(Err::disp).sorted(), "", " or ", ""); }
  private Err typeNotWellKinded(String first, T.C c, int index, String allowedStr, String gotStr){
    var bad= c.ts().get(index);
    var bs= decs.apply(c.name()).bs();
    return err().pTypeArgBounds(first, err().tNameADisp(c.name()), disp(bs.get(index).x()), index, bad, allowedStr, gotStr);
  }
  private Err typeNotWellKindedSig(T.C t, E.Call c, int index, String allowedStr, String gotStr){
    var d= decs.apply(t.name());
    var m= OneOr.of("Malformed methods", d.ms().stream().filter(mi -> mi.sig().m().equals(c.name()) && mi.sig().rc() == c.rc()));
    var param= m.sig().bs().get(index);
    var decName= err().methodSig(c.rc().toStrSpace(), d, c.name()); // p.A.m(...)
    var bad= c.targs().get(index);
    return err().pTypeArgBounds("This call to method "+decName+" cannot typecheck.", decName, disp(param.x()), index, bad, allowedStr, gotStr);
  }
  private List<T> inferredInParam(Literal d, Call c, int argi){
    if (!Err.inferredTargs(c)){ return List.of(); }
    var s= OneOr.of("Malformed methods", d.ms().stream().map(M::sig).filter(si -> si.m().equals(c.name()) && si.rc() == c.rc()));
    var param= s.ts().get(argi);
    return IntStream.range(0, s.bs().size())
      .filter(i -> mentions(param, s.bs().get(i).x()))
      .mapToObj(c.targs()::get)
      .toList();
  }
  private static boolean mentions(T t, String x){ return switch (t){
    case T.X(var n, _) -> n.equals(x);
    case T.RCX(_, var tx) -> tx.name().equals(x);
    case T.ReadImmX(var tx) -> tx.name().equals(x);
    case T.RCC(_, var c, _) -> c.ts().stream().anyMatch(ti -> mentions(ti, x));
  };}
  ///Overriding method in literal l is not a valid subtype of inherited method.
  ///Raised when checking object literals
  public FearlessException methodOverrideSignatureMismatchContravariance(TypeSystem ts, List<B> ctx, Literal l, Sig current, Sig parent, int index){
    assert current.m().equals(parent.m());
    var parentArg= parent.ts().get(index);
    var currentArg= current.ts().get(index);
    assert !ts.isSub(ctx, parentArg, currentArg);
    var inverse= ts.isSub(ctx, currentArg, parentArg)
      ? "It is instead a supertype: you are strengthening the parameter instead of weakening it."
      : "The two types are unrelated.";
    return overrideErr(l, current, parent,
      "accepts parameter "+(index+1)+" of type "+err().typeRepr(true, currentArg),
      "requires "+err().typeRepr(true, parentArg)+", which is not a subtype of "+err().typeRepr(true, currentArg),
      inverse);
  }
  public FearlessException methodOverrideArgCapabilityChanged(Literal l, Sig current, Sig parent, int index){
    return overrideErr(l, current, parent,
      "accepts parameter "+(index+1)+" of type "+err().typeRepr(false, current.ts().get(index)),
      "requires "+err().typeRepr(false, parent.ts().get(index)),
      capabilityLocked);
  }
  public FearlessException methodOverrideRetCapabilityChanged(Literal l, Sig current, Sig parent){
    return overrideErr(l, current, parent,
      "returns type "+err().typeRepr(false, current.ret()),
      "returns type "+err().typeRepr(false, parent.ret()),
      capabilityLocked);
  }
  private static final String capabilityLocked= "An overriding method can refine the types of its parameters and result, but not their reference capabilities.";
  ///Overriding method in literal l is not a valid subtype of inherited method.
  ///Raised when checking object literals
  public FearlessException methodOverrideSignatureMismatchCovariance(TypeSystem ts, List<B> ctx, Literal l, Sig current, Sig parent){
    assert current.m().equals(parent.m());
    var parentRet= parent.ret();
    var currentRet= current.ret();
    assert !ts.isSub(ctx, currentRet, parentRet);
    var inverse= ts.isSub(ctx, parentRet, currentRet)
      ? "It is instead a subtype: you are weakening the result instead of strengthening it."
      : "The two types are unrelated.";
    return overrideErr(l, current, parent,
      "returns type "+err().typeRepr(true, currentRet),
      "returns type "+err().typeRepr(true, parentRet)+", which is not a supertype of "+err().typeRepr(true, currentRet),
      inverse);
  }
  ///A required method was left abstract instead of being implemented.
  ///Raised when checking object literals
  public FearlessException callableMethodStillAbstract(E at, M got){
    var s= got.sig();
    var e= err()
      .line("This object literal is missing a required method.")
      .line("Missing: "+methodSig(s.rc()+" ", s.m())+".")
      .line(Join.of(requiredBy(at, s).stream().map(err()::tNameADisp), "Required by: ", " and ", "."));
    if (s.rc() == RC.mut){ e.line("This object literal is neither "+disp(RC.imm)+" nor "+disp(RC.read)+", so its "+disp(RC.mut)+" methods must be implemented."); }
    if (!(at instanceof Type t && foreignSealed(t.type().c().name()))){ return addExpFrame(at, e.line("Hint: add an implementation for "+err().methodSig(s.m())+" inside the object literal.").ex(at)); }
    var name= t.type().c().name();
    return addExpFrame(at, e
      .line("Sealed types can only be implemented in their own package.")
      .line("Type "+err().tNameADisp(name)+" is in package "+disp(Package.writtenPkg(pkg.map(), name.pkgName()))+".")
      .ex(at));
  }
  private List<TName> requiredBy(E at, Sig s){
    if (!(at instanceof Literal l) || !s.origin().equals(l.name())){ return List.of(s.origin()); }
    return l.cs().stream().flatMap(c -> decs.apply(c.name()).ms().stream()).map(M::sig)
      .filter(si -> si.abs() && si.m().equals(s.m()) && si.rc() == s.rc()).map(Sig::origin).distinct().toList();
  }
  private boolean foreignSealed(TName name){
    return !name.pkgName().equals(pkg.name()) && LiteralDeclarations.has(decs.apply(name).cs(), LiteralDeclarations.sealed);
  }
  public FearlessException literalImplementsTypeParameter(E at, T req){
    var x= err().typeRepr(true, req);
    var untyped= at instanceof Literal l && l.src().inner instanceof fearlessFullGrammar.E.Literal;
    if (untyped){ return addExpFrame(at, err()
      .line(up(err().expRepr(at))+" cannot implement "+x+".")
      .line(x+" is a generic type parameter; object literals can only implement nominal types.")
      .typeErr());
    }
    E typed= switch (at){ case Literal l -> l.withRC(RC.imm); case Type t -> new Type(t.type().withRC(RC.imm), t.src()); default -> throw Bug.unreachable(); };
    return addExpFrame(at, err()
      .line(up(err().expRepr(typed))+" is required to be of type "+x+".")
      .line(x+" is a generic type parameter; an object literal is always of a nominal type.")
      .typeErr());
  }
  public FearlessException typeDeclaredInMethod(E at, Literal l){
    return addExpFrame(at, err()
      .line("The type "+err().tNameADisp(l.name())+" is not standalone: it is declared inside a method body.")
      .line("Only a standalone type can be implemented or mentioned by name.")
      .line("A type is standalone if it is declared at top level, or if it implements "+err().tNameADisp(LiteralDeclarations.captureFree)+".")
      .ex(at));
  }
  ///Implemented method can never be called for any receiver obtained from the literal.
  ///Its body is statically dead code (typically a mut method on an imm/read literal).
  ///Raised when checking object literals
  public FearlessException methodImplementationDeadCode(M got, Literal l){
    var s= got.sig();
    assert s.rc() == RC.mut;
    assert l.rc().isReadOrImm();
    var m= methodSig(s.rc()+" ", s.m());
    var e= err()
      .line("The method "+err().methodSig(s.rc().toStrSpace(), l, s.m())+" is dead code.")
      .line("The "+err().expRepr(l.withRC(RC.imm))+" is "+disp(l.rc())+", so it will never be seen as "+disp(RC.mut)+".");
    e.line(inheritedSig(l, got).orElse("But it implements method "+m+", which requires a "+disp(RC.mut)+" receiver."));
    renamedGenerics(l, got).ifPresent(e::line);
    return addExpFrame(l, e.typeErr().addSpan(s.span().inner));
  }
  public FearlessException selfNameDeadCode(Literal l){
    return addExpFrame(l, err()
      .line("The self name "+disp(l.thisName())+" is dead code.")
      .line("No method of the "+err().expRepr(l)+" uses it.")
      .line("Remove "+disp("'"+l.thisName())+" from the object literal.")
      .ex(l));
  }
  ///Iso parameter is used in a way that violates affine discipline.
  ///Allowed uses: capture into object literals as imm, or use directly at most once.
  ///if !earlyErrOnMoreThenOnceDirectly then used exactly once directly but ALSO used in literals
  ///Raised when checking object literals
  public FearlessException notAffineIso(Literal l, M m, String name, boolean earlyErrOnMoreThenOnceDirectly, List<E.X> usages){
    assert !usages.isEmpty();
    var line= m.sig().span().inner.startLine();
    var ms= err().methodSig(m.sig().rc().toStrSpace(), l, m.sig().m());
    var p= pattern(l, m, name, usages.getFirst());
    var x= disp(p.map(FearlessErrFactory::patternRepr).orElse(usages.getFirst().src().inner instanceof fearlessFullGrammar.E.Implicit ? "::" : name));
    var t= m.sig().ts().get(m.xs().indexOf(name));
    var iso= t instanceof T.RCC r && r.rc() == RC.iso || t instanceof T.RCX rx && rx.rc() == RC.iso;
    var e= err();
    if (!iso){ e.line("Parameter "+x+" of type "+err().typeRepr(false, t)+", which can be instantiated with "+disp(RC.iso)); }
    e.line("The iso parameter "+x+" violates the single-use rule in method "+ms+" (line "+line+").");
    p.filter(_ -> earlyErrOnMoreThenOnceDirectly).ifPresent(d -> e.line("The pattern "+x+" calls "+Join.of(d.extract().stream().map(ns -> disp(ns.getFirst().s())), "", " and ", "")+" on it."));
    var ex= e.line(earlyErrOnMoreThenOnceDirectly ? "It is used directly "+usages.size()+" times." : "It is used directly and also captured into object literals.")
      .line("An iso parameter can either be captured into object literals, or be used directly once.")
      .typeErr();
    for (var u : usages){ ex.addSpan(u.span().inner); }
    return ex;
  }
  private static Optional<fearlessFullGrammar.XPat.Destruct> pattern(Literal l, M m, String name, E.X usage){
    if (usage.src().inner instanceof fearlessFullGrammar.E.Implicit){ return Optional.empty(); }
    var xp= srcM(l, m.sig()).get().sig().get().parameters().get(m.xs().indexOf(name)).xp().get();
    return xp instanceof fearlessFullGrammar.XPat.Destruct d ? Optional.of(d) : Optional.empty();
  }
  ///Expression at method body has a type that does not meet its result requirement(s).
  ///"body has wrong type" error; can only trigger if all current-expressions at are well typed.
  ///Raised when checking object literals
  public FearlessException methodBodyWrongType(TypeScope.Method s, E at, Reason got){
    var l= s.l();
    var m= s.m();
    assert !got.isEmpty();
    var got0= err().typeRepr(!got.showImm, got.best);
    var e= err();
    var meth= err().methodSig(m.sig().m());
    var top= l.thisName().equals("this");
    e.line(top
      ? "The body of method "+meth+" of "+err().expRepr(l)+" is an expression returning "+got0+"."
      : "Method "+meth+" inside the "+err().expRepr(l)+" (line "+l.span().inner.startLine()+")"
        +"\nis implemented with an expression returning "+got0+".");
    e.line(up(got.info(printed)));
    inheritedSig(l, m).ifPresent(e::line);
    for (TypeScope it= s; !it.isTop(); it = it.outer()){
      if (it instanceof TypeScope.Method(var li, var mi, _)){ renamedGenerics(li, mi).ifPresent(e::line); }
    }
    var thisNotMut= at instanceof X x && x.name().equals(l.thisName()) && m.sig().rc() == RC.mut && LiteralDeclarations.has(l.cs(), LiteralDeclarations.captureFree);
    if (thisNotMut){ e.line("Hint: "+err().expRepr(l)+" implements "+err().tNameADisp(LiteralDeclarations.captureFree)+", so parameter "+disp(l.thisName())+" is \"imm\" in every method."); }
    overloadHint(e, l, m);
    return addExpFrame(at, e.ex(got.footerE.get(), at).addSpan(at.span().inner));
  }
  private void overloadHint(Err e, Literal l, M m){
    var written= srcM(l, m.sig()).flatMap(fearlessFullGrammar.M::sig).flatMap(fearlessFullGrammar.Sig::rc).isPresent();
    var overloads= l.ms().stream().map(M::sig).filter(s -> !s.abs() && s.m().equals(m.sig().m())).map(s -> methodSig(s.rc()+" ", s.m())).toList();
    if (written || overloads.size() < 2){ return; }
    e.line("Method "+err().methodSig(m.sig().m())+" is overloaded; to implement a specific overload only, write one of the following:");
    overloads.forEach(e::bullet);
  }


  ///Parameter x is syntactically in scope but its value was dropped by viewpoint adaptation.
  ///Raised when a use of x occurs after capturing have made it unavailable.
  ///Raised when checking parameters.
  public FearlessException parameterNotAvailableHere(TypeScope s, E.X x, Change.NoT why){
    var e= err().line(whyDrop(x, why));
    var site= why instanceof Change.DropMutInImm
      ? Stream.iterate(s, si -> !si.isTop(), TypeScope::outer).filter(si -> inferredRcOf(si, why.l())).findFirst()
      : Optional.<TypeScope>empty();
    var ex= site.map(si -> e.ex(si.contextE(), si.contextE())).orElseGet(() -> e.ex(x));
    return addExpFrame(x, ex.addSpan(x.span().inner));
  }
  private static boolean inferredRcOf(TypeScope s, Literal l){
    var interest= l.cs().stream().<T>map(c -> new T.RCC(l.rc(), c, l.span())).toList();
    return s instanceof TypeScope.CallSite(var c, _) && Err.inferredTargs(c) && TypeScope.mentionsAny(s, interest);
  }
  private String whyDrop(E.X x, Change.NoT why){
    var subject= err().expRepr(x);
    return switch (why){
      case Change.DropMutInImm _ -> whyDropMutInImm(subject, why);
      case Change.DropReadHMutH _ -> whyDropReadHMutH(subject, why);
      case Change.DropNotKinded _ -> whyDropNotKinded(subject, why);
      case Change.DropFTV _ -> throw Bug.unreachable();
      case Change.CapFree _ -> whyDropCapFree(subject, x.span().inner.startLine(), why);
    };
  }
  private String whyDropMutInImm(String subject, Change.NoT why){
    if (why.atDrop() instanceof T.X && !why.l().infName()){ return up(subject)+" has type "+err().typeRepr(true, why.atDrop())+".\n"
      +"The generic type parameters of "+err().expRepr(why.l())+" (line "+why.l().span().inner.startLine()+") are "+disp(Join.of(why.l().bs(), "", ", ", "", ""))+".\n"
      +"Under those bounds, "+subject+" can observe mutation.\n"
      +"Thus "+subject+" cannot be captured in that "+disp(why.l().rc())+" object literal.";
    }
    return up(subject)+" has type "+err().typeRepr(true, why.atDrop())+".\n"
    +up(subject)+" can observe mutation; thus it cannot be captured in the "+disp(why.l().rc())+" "+err().expRepr(why.l())
    +" (line "+why.l().span().inner.startLine()+").\n"
    +"Hint: capture an immutable copy instead, or move this use outside the object literal.";
  }
  private String whyDropNotKinded(String subject, Change.NoT why){
    var bounds= disp(Join.of(why.l().bs(), "", ", ", "", ""));
    return up(subject)+" has type "+err().typeRepr(true, why.atDrop())+".\n"
    +"That type is not well kinded under the generic type parameters of "+err().expRepr(why.l())
    +" (line "+why.l().span().inner.startLine()+"): "+bounds+".\n"
    +"The bounds declared by the object literal are all it knows about its generic type parameters,\n"
    +"and thus "+subject+" cannot be captured.\n";
  }
  private String whyDropReadHMutH(String subject, Change.NoT why){
    var explicitH= why.atDrop().explicitH()
      ? "The type of "+subject+" is hygienic (readH or mutH)\n"
      : "The type of "+subject+" can be instantiated with a hygienic capability (readH or mutH)\n";
    return up(subject)+" has type "+err().typeRepr(true, why.atDrop())+".\n"
    +explicitH+"and thus it cannot be captured in the "+err().expRepr(why.l())
    +" (line "+why.l().span().inner.startLine()+").\n";
  }
  private String whyDropCapFree(String subject, int useLine, Change.NoT why){
    return
    up(err().expRepr(why.l()))+" (line "+why.l().span().inner.startLine()+") implements "+err().tNameADisp(LiteralDeclarations.captureFree)+".\n"
    +"Thus "+subject+" (line "+useLine+") cannot be captured in that object literal.\n";
  }
  ///Receiver expression of call c is typed into a type parameter (X / RC X / read/imm X), not a concrete RC C.
  ///Methods cannot be called on type parameters, so this call can never resolve.
  ///Raised when checking method calls.
  public FearlessException methodReceiverIsTypeParameter(TypeScope s, Call c, T recvType){
    var best= TypeScope.bestInterestingScope(s, List.of(recvType));
    return withCallSpans(err()
      .pCallCantBeSatisfied(c)
      .line("The receiver has type "+err().typeRepr(true, recvType)+", where "+disp(((T.RCX)recvType.withRC(RC.imm)).x().name())+" is a generic type parameter.")
      .line("Generic type parameters cannot be receivers of method calls.")
      .ex(best.contextE(), c.e()), c.e(), c);
  }
  ///No method matches call c.
  ///Sub-errors for more clarity
  /// - no such name at all; searching for similar names with "Did you mean..."
  /// - method name exist but with different arity; error will list those other method signatures
  /// - method exists with right arity, but different receiver RCs; list those other method signatures
  ///Raised when checking method calls.
  public FearlessException methodNotDeclared(TypeScope scope, Call c, Literal d){
    var di= d.withRC(RC.imm);
    var _on= err().onTypeOrAnon(di);
    var subj= err().theTypeOrObjectLiteral(di);
    var on= c.e().equals(d) ? _on : subj;
    var e= err()
      .pCallCantBeSatisfied(c)
      .line("Method "+err().methodSig(c.name())+" is not declared on "+on+".");
    var name= c.name().s();
    var candidates= d.ms().stream().map(M::sig).toList();
    var sameName= candidates.stream()
      .filter(s -> s.m().s().equals(name)).toList();
    if (sameName.isEmpty()){
      addEnclosingLiteralHintIfReceiverIsThis(e, scope, c, name, subj);
      if (candidates.isEmpty()){ return withCallSpans(e.line(up(subj)+" does not have any methods.").typeErr(), c); }
      var names= candidates.stream().map(s -> s.m().s()).distinct().sorted().toList();
      NameSuggester.suggest(name, names, (_,cs,best) -> { bestNameMsg(e, on, candidates, cs, best); return null; } );
      return withCallSpans(e.typeErr(), c);
    }
    var sameArity= sameName.stream().filter(s -> s.m().arity() == c.es().size()).toList();
    if (sameArity.isEmpty()){
      var avail= Join.of(sameName.stream().map(s -> s.m().arity()).distinct().sorted().map(String::valueOf), "", " or ", "");
      var forms= sameName.stream().map(s -> methodSig("", s.m())).distinct().sorted().toList();
      return withCallSpans(err()
        .pCallCantBeSatisfied(c)
        .line((forms.size() == 1 ? "There is a method " : "There are methods ")+Join.of(forms, "", " and ", "")+" on "+on+",\nbut with a different number of arguments.")
        .line("This call supplies "+c.es().size()+", but available methods take "+avail+".")
        .typeErr(), c);
    }
    var rcs= sameArity.stream().map(Sig::rc).sorted().toList();
    var availRc= Join.of(rcs.stream().map(Err::disp), "", " and ", ".");
    return withCallSpans(err()
      .pCallCantBeSatisfied(c)
      .line("Method "+err().methodSig(c.name())+" exists on "+on+", but not with the requested capability.")
      .line("This call requires a method with capability "+disp(c.rc())+".")
      .line("Available capabilities for this method: "+availRc)
      .typeErr(), c);
  }
  static boolean isSelfName(TypeScope s, String x){
    return Stream.iterate(s, si -> !si.isTop(), TypeScope::outer).anyMatch(si -> si instanceof TypeScope.Method(var l, _, _) && l.thisName().equals(x));
  }
  private void addEnclosingLiteralHintIfReceiverIsThis(Err e, TypeScope scope, Call c, String name, String on){
    var receiverIsThis= c.e() instanceof X(var xName, _) && xName.equals("this");
    if (!receiverIsThis){ return; }
    for (var s= scope; !s.isTop(); s = s.outer()){
      if (!(s instanceof TypeScope.Method(var l, _, _))){ continue; }
      var has= l.ms().stream().anyMatch(m -> m.sig().m().s().equals(name));
      if (!has){ continue; }
      var sig= err().methodSig(c.name());
      var lit= l.infName() ? err().bestNameNoRc(l) : "of type "+err().tNameADisp(l.name());
      var selfName= l.thisName();
      e.line("Hint:")
       .line("The method parameter \"this\" here has "+on+".")
       .blank();
      if (!selfName.equals("_")){
        e.line("The method "+sig+" is defined in the object literal "+lit+"; the parameter "
             +"referring to its instances is named "+disp(selfName)+".");
        return;
      }
      e.line("The method "+sig+" is defined in the object literal "+lit+".")
       .line("No parameter refers to instances of this literal.")
       .line("To declare one, use the single quote as in the example below:")
       .line("  Rectangles: { #(width: Nat, height: Nat): Rectangle -> Rectangle:{'rect")
       .line("    .area: Nat -> width * height;")
       .line("    .str: Str -> \"area: \"+(rect.area.str);")
       .line("    .withWidth(width': Nat): Rectangle -> this#(width', height);")
       .line("  }}");
      return;
    }
  }
  void bestNameMsg(Err e, String onStr, List<Sig> candidates, List<String> cs, Optional<String> best){
    best.ifPresent(b -> e.line("Did you mean "+disp(b)+" ?"));
    e.blank().line("Available methods on "+onStr+":");
    for (var n : cs){
      candidates.stream()
        .filter(s -> s.m().s().equals(n))
        .forEach(s -> e.bullet(e.cp().sig(s)));
    }
  }
  ///A method matching c by name / arity / RC exists, but c supplies the wrong number of type arguments.
  ///Triggered only for explicitly written [Ts]; inference never reaches this error.
  ///Raised when checking method calls.
  public FearlessException methodTArgsArityError(Literal d, Call c, List<B> bs){
    var expected= bs.size();
    var got= c.targs().size(); assert got != expected;
    var sig= err().methodSig(c.name());
    var expS= expected == 0 ? "no generic type parameters" : count(expected, "generic type parameter");
    var gotS= got == 0 ? "no generic type arguments" : count(got, "generic type argument");
    var e= err().pCallCantBeSatisfied(d, c)
      .line("Wrong number of generic type arguments for "+sig+".")
      .line("Method "+sig+" declares "+expS+".");
    if (expected != 0){ e.line("Declared generic type parameters: "+Join.of(bs.stream().map(b -> disp(b.x())), "", ", ", ".")); }
    return withCallSpans(e.line("This call provides "+gotS+".").typeErr(), c);
  }
  ///Methods exist for call c, but the receiver capability is too weak for all the available promotions.
  ///No promotion accepts this receiver, so the call cannot succeed regardless of argument types.
  ///Raised when checking method calls.
  public FearlessException receiverRCBlocksCall(TypeScope s, Literal d, Call c, RC recvRc, List<MType> promos, Gamma g){
    var needed= promos.stream().map(MType::rc).distinct().sorted().map(Err::disp).toList();
    var e= err()
      .pCallCantBeSatisfied(d, c)
      .line("The receiver (the expression before the method name) has capability "+disp(recvRc)+".")
      .line(Join.of(needed, "This call requires a receiver with capability ", " or ", "."));
    if (c.e() instanceof X x && g.bind(x.name()).current() instanceof Change.WithT w && !(w instanceof Change.Same)){ e.line(Reason.adaptation(this, isSelfName(s, x.name()), x, w)); }
    if (c.e() instanceof X x && g.bind(x.name()).current() instanceof Change.Same(T.RCC t) && t.rc() == RC.imm && !isSelfName(s, x.name())){
      e.line(up(err().expRepr(x))+" has type "+err().typeRepr(false, t)+": a type written without a capability, as "+err().typeRepr(true, t)+", is \"imm\".");
    }
    return withCallSpans(e.pReceiverRequiredByPromotion(promos).ex(c), c.e(), c);
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
  public FearlessException methodArgumentCannotMeetAnyPromotion(TypeSystem ts, List<B> bs, Literal d, Call c, int argi, T declared, List<TRequirement> reqs, List<Reason> res){
    assert argi >= 0;
    assert argi < c.es().size();
    assert !reqs.isEmpty();
    assert reqs.size() == res.size();
    assert res.stream().noneMatch(Reason::isEmpty);
    assert reqs.stream().allMatch(r -> canon(r.t()).equals(canon(declared)));
    if (isWrongUnderlyingType(ts, bs, canon(declared), res)){ return wrongUnderlyingTypeErr(ts, bs, d, c, argi, declared, res); }
    var gotHdr= headerBest(res);
    var r= Streams.zip(res, reqs).filter((ri,q) -> rcOnlyMismatch(ri.best, q.t())).map((ri,_) -> ri).findFirst().orElse(res.getFirst());
    var e= err()
      .pCallCantBeSatisfied(d, c)
      .line("Argument "+(argi+1)+" has type "+err().typeRepr(false, gotHdr)+".")
      .line(up(r.info(printed)))
      .blank()
      .line("Type required by each promotion:");
    reqs.forEach(q -> e.bullet(err().typeRepr(false, q.t())+" ("+q.reqName()+")"));
    addNoPrecedenceHintIfOperator(e, ts.scope(), c);
    var footer= r.footerE.get();
    return withCallSpans(e.ex(footer, c.es().get(argi), inferredInParam(d, c, argi)), c.es().get(argi), c);
  }
  private FearlessException wrongUnderlyingTypeErr(TypeSystem ts, List<B> bs, Literal d, Call c, int argi, T declared, List<Reason> res){
    var gotHdr= headerBest(res);//TODO: Eventually this will need to be matched with the meth body subtype and both
    //should make an attempt to say what the generics in the result should have been instantiate to instead
    //in particular here we are in a methCall, so we can talk about OUR type args impacting the expected argument type
    var inferred= inferredInParam(d, c, argi);
    var e= err()
      .pCallCantBeSatisfied(d, c)
      .line("Argument "+(argi+1)+" has type "+err().typeRepr(true, gotHdr)+".")
      .line("That is not a subtype of "+err().typeRepr(true, declared)+(inferred.isEmpty() ? " (the type required by the method signature)." : "."));
    if (lambdaFits(ts, bs, declared, gotHdr)){ e.line("Hint: write the argument inside curly braces: the curly braces make an object literal instance of "+err().typeRepr(true, declared.withRC(RC.imm))+", whose single method returns the argument."); }
    addNoPrecedenceHintIfOperator(e, ts.scope(), c);
    return withCallSpans(e.ex(c, c.es().get(argi), inferred), c.es().get(argi), c);
  }
  private boolean lambdaFits(TypeSystem ts, List<B> bs, T declared, T got){
    if (!(declared instanceof T.RCC(_, var c, _)) || foreignSealed(c.name())){ return false; }
    var d= decs.apply(c.name());
    var abs= d.ms().stream().map(M::sig).filter(Sig::abs).toList();
    if (abs.size() != 1 || !abs.getFirst().ts().isEmpty()){ return false; }
    return ts.isSub(bs, got, TypeRename.of(abs.getFirst().ret(), B.xs(d.bs()), c.ts()));
  }
  private void addNoPrecedenceHintIfOperator(Err e, TypeScope s, Call c){
    var name= c.name().s();
    var notOperator= name.startsWith(".") || name.equals("#");
    var receiver= s.outer() instanceof TypeScope.CallSite(var p, _) && p.e() == c;
    if (notOperator || !receiver){ return; }
    e.line("Hint: all method names have the same precedence, so an expression like \"a.get + b.get\" "
         +"parses as \"(a.get + b).get\", not \"a.get + (b.get)\". "
         +"If this argument needed a method applied to it first, wrap it in parentheses.");
  }
  private static boolean isWrongUnderlyingType(TypeSystem ts, List<B> bs, T reqCanon, List<Reason> res){
    return res.stream().map(r -> canon(r.best)).noneMatch(r -> ts.isSub(bs, r, reqCanon));
  }
  private static T canon(T t){ return t.withRC(RC.imm); }

  private static T headerBest(List<Reason> res){
    return res.stream().map(r -> r.best)
      .min(Comparator.comparingInt(TypeSystemErrors::headerKey))
      .get();
  }
  private static int headerKey(T t){ return switch (t){
    case T.RCC(var rc, _, _) -> rc.ordinal();
    case T.RCX(var rc, _) -> rc.ordinal();
    case T.X _ -> 1000;
    case T.ReadImmX _ -> 1001;
  };}
  ///Each argument of call c is compatible with at least one promotion, but no promotion fits all arguments.
  ///The per-argument sets of acceptable promotions have empty intersection.
  ///Raised when checking method calls.
  ///Error details
  ///  - What arguments satisfy what promotion and why (best type <: required type1, required type 2 etc)
  public FearlessException methodPromotionsDisagreeOnArguments(Literal d, Call c, ArgMatrix mat){
    var args= mat.okByArg().size();
    assert args > 0;
    assert mat.resByArg().size() == args;
    var e= err()
      .pCallCantBeSatisfied(d, c)
      .line("Each argument is compatible with at least one promotion, but no single promotion fits all arguments.")
      .blank()
      .line("Compatible promotions by argument:");
    for (int argi : Range.of(0, args)){
      var ok= mat.okByArg().get(argi);
      assert !ok.isEmpty();
      var promos= ok.stream().map(i -> mat.candidate(i).promotion()).distinct().sorted().toList();
      var got= err().typeRepr(false, headerBest(mat.resByArg().get(argi)));
      e.bullet("Argument "+(argi+1)+" has type "+got+" and is compatible with: "+Join.of(promos, "", ", ", "")+".");
    }
    e.blank().line("Promotion failures:");
    var byArg= IntStream.range(0, args)
      .mapToObj(_ -> new LinkedHashMap<String,ArrayList<String>>()).toList();
    var promosN= mat.resByArg().getFirst().size();
    for (int pi : Range.of(0, promosN)){
      var argi= IntStream.range(0, args).filter(a -> !mat.okByArg().get(a).contains(pi)).findFirst().getAsInt();
      var r= mat.resByArg().get(argi).get(pi);
      assert !r.isEmpty();
      byArg.get(argi).computeIfAbsent(up(r.info(printed)), _ -> new ArrayList<>())
        .add(mat.candidate(pi).promotion());
    }
    for (int argi : Range.of(0, args)){
      byArg.get(argi).forEach((info,names) -> e.bullet("Argument "+(argi+1)+Join.of(names, " fails:    ", ", ", "\n")+info));
    }
    return withCallSpans(e.ex(c), c);
  }
}