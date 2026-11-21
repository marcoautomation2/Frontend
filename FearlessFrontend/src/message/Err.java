package message;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.Locale;
import java.util.Optional;

import core.*;
import core.E.*;
import inject.TypeRename;
import metaParser.Message;
import metaParser.Span;
import typeSystem.TypeSystem.*;
import utils.Bug;
import utils.Join;
import utils.Push;
import utils.Streams;

public record Err(Function<T.C,T.C> publicHead, Function<TName,TName> preferredForFresh, Function<TName,Literal> _decs, Function<Boolean,CompactPrinter> _cp, Supplier<List<String>> notes, StringBuilder sb){
  CompactPrinter cp(){ return _cp.apply(false); }
  public static String disp(Object o){ return Message.displayString(o.toString()); }
  static String funnel(String X, String owner, List<String> Xs){
    var x= disp(X);
    var dec= disp(owner);
    var declares= Xs.isEmpty() ? "none" : Join.of(Xs.stream().map(Err::disp), "", ", ", "", "");
    var funnelled= disp(Join.of(Push.of(Xs, X).stream().map(s -> s+":.."), owner+"[", ",", "]", ""));
    return "Generic type parameter "+x+" is not in scope inside the type declaration "+dec+".\n"
      +"A type declaration only sees the generic type parameters it declares itself; here "+dec+" declares "+declares+".\n"
      +"Hint: funnel "+x+" into "+dec+" by writing "+funnelled+", restating the bounds of "+x+".";
  }
  public static String genArity(int n){ return Join.of(Collections.nCopies(n, "_"), "[", ",", "]", ""); }
  static String staticTypeDecName(TName name){ return disp(name.simpleName()+genArity(name.arity())); }//for the parser and the well formedness errors only
  static <A> A redeclaredElement(List<A> es){
    return IntStream.range(0, es.size())
      .filter(i -> i != es.lastIndexOf(es.get(i)))
      .mapToObj(es::get)
      .findFirst().get();
  }

  String tNameA(TName n){ return cp().t.of(n)+genArity(n.arity()); }     // "A[_]"
  String tNameADisp(TName n){ return disp(tNameA(n)); }                      // displayString("A[_]")
  private boolean showInstanceOf(Literal l){ return l.infName() && !l.cs().isEmpty(); }
  private String bestLitName(boolean skipRc, boolean skipImm, Literal l){
    var rc= skipRc ? RC.imm : l.rc();
    if (showInstanceOf(l)){ return typeReprRaw(skipImm || skipRc, new T.RCC(rc, l.cs().getFirst(), l.span())); }
    if (anonLit(l)){ return anonRepr; }
    return rc.toStrSpace(skipImm)+tNameA(l.name());
  }
  private String bestLitName(inference.E.Literal l){
    if (!l.infName()){ return tNameA(l.name()); }
    return tNameA(!l.cs().isEmpty() ? l.cs().getFirst().name() : l.t() instanceof inference.IT.RCC r ? r.c().name() : l.name());
  }
  private String bestNamePkg0(boolean instanceOf, String n){
    return (instanceOf ? "instance of " : "")+disp(n);
  }
  private boolean anonLit(Literal l){ return l.infName() && l.cs().isEmpty(); }
  private static final String anonRepr= "{...}";
  String onTypeOrAnon(Literal l){ return anonLit(l) ? disp(anonRepr) : "object literal instance of "+disp(bestLitName(true, true, l)); }
  String theTypeOrObjectLiteral(Literal l){ return anonLit(l) ? "object literal "+disp(anonRepr) : "type "+disp(bestLitName(false, true, l)); }
  public String bestNameNoRc(Literal l){ return bestNamePkg0(showInstanceOf(l), bestLitName(true, true, l)); }
  T.C preferredForFresh(T.C t){ return new T.C(preferredForFresh.apply(t.name()).withArity(t.ts().size()), t.ts()); }//Correct to not propagate here
  String typeRepr(inference.IT t){ return typeRepr(true, t); }
  String typeRepr(boolean skipImm, inference.IT t){ return t.isTV() ? typeRepr(skipImm, TypeRename.itToT(t)) : disp(typeReprRaw(t)); }
  String typeReprRaw(inference.IT t){ return switch (t){
    case inference.IT.RCC(var rc, var c, _) -> rc.map(RC::toStrSpace).orElse("")+cp().t.of(c.name())+Join.of(c.ts().stream().map(this::typeReprRaw), "[", ",", "]", "");
    case inference.IT.U _, inference.IT.Amb _ -> "?";
    default -> typeReprRaw(true, TypeRename.itToT(t));
  };}
  String typeRepr(inference.IT t, int levels){ return disp(typeReprRaw(t, levels)); }
  private String typeReprRaw(inference.IT t, int levels){
    if (!(t instanceof inference.IT.RCC(var rc, var c, _)) || c.ts().isEmpty()){ return typeReprRaw(t); }
    var ts= levels == 0 ? "[...]" : Join.of(c.ts().stream().map(ti -> typeReprRaw(ti, levels-1)), "[", ",", "]", "");
    return rc.map(RC::toStrSpace).orElse("")+cp().t.of(c.name())+ts;
  }
  String typeRepr(boolean skipImm, T t){
    if (t instanceof T.RCC r && _anon(r.c().name()) instanceof Literal l){ return "the anonymous type of the object literal at "+at(l.span().inner); }
    return disp(typeReprRaw(skipImm, t));
  }
  private Literal _anon(TName n){
    var d= _decs.apply(n);
    if (d == null || !d.infName() || d.cs().stream().anyMatch(c -> !_decs.apply(c.name()).infName())){ return null; }
    return d;
  }
  static String at(Span s){ return "line "+s.startLine()+", column "+s.startCol(); }
  private String typeReprRaw(boolean skipImm, T t){
    var str= cp().msgT(showPublic(t));
    var noImmPrefix= skipImm || !(t instanceof T.RCC rcc && rcc.rc() == RC.imm);
    if (noImmPrefix){ return str; }
    return "imm "+str;
  }
  private T showPublic(T t){
    if (!(t instanceof T.RCC(var rc, var c, var span))){ return t; }
    var p= publicHead.apply(c);
    return new T.RCC(rc, p.withTs(p.ts().stream().map(this::showPublic).toList()), span);
  }
  String typeRepr(T.C t){ return disp(cp().msgT(new T.RCC(RC.imm, preferredForFresh(t), t.span()))); }
  static String count(int n, String noun){ return n+" "+noun+(n == 1 ? "" : "s"); }
  static String up(String s){ return s.substring(0, 1).toUpperCase(Locale.ROOT)+s.substring(1); }
  static Optional<fearlessFullGrammar.M> srcM(Src src, Sig s){
    List<fearlessFullGrammar.M> ms= switch (src.inner){
      case fearlessFullGrammar.Declaration d -> d.l().methods();
      case fearlessFullGrammar.E.Literal gl -> gl.methods();
      case fearlessFullGrammar.E.TypedLiteral t -> t.l().map(fearlessFullGrammar.E.Literal::methods).orElse(List.of());
      default -> throw Bug.unreachable();
    };
    return utils.OneOr.opt("Malformed methods", ms.stream().filter(mi -> mi.span().inner.equals(s.span().inner)));
  }
  Optional<String> renamedGenerics(Function<TName,Literal> decs, Src src, List<TName> parents, Sig s){
    var fm= srcM(src, s);
    var written= fm.flatMap(fearlessFullGrammar.M::sig).flatMap(fearlessFullGrammar.Sig::bs).isPresent();
    if (fm.isEmpty() || written){ return Optional.empty(); }
    var declared= parents.stream().flatMap(p -> decs.apply(p).ms().stream().map(M::sig).filter(ps -> ps.origin().equals(p) && ps.m().equals(s.m()) && ps.rc() == s.rc())).toList();
    return declared.stream().filter(ps -> declared.stream().noneMatch(qs -> isSuper(decs, ps.origin(), qs.origin()))).findFirst()
      .flatMap(ps -> renamed(methodSig("", ps.origin(), ps.m()), ps.bs(), s.bs()));
  }
  private static boolean isSuper(Function<TName,Literal> decs, TName sup, TName sub){ return decs.apply(sub).cs().stream().anyMatch(c -> c.name().equals(sup)); }
  static Optional<String> renamed(String parentSig, List<B> declared, List<B> here){
    var renamed= Streams.zip(declared, here).filter((d,h) -> !d.x().equals(h.x()));
    var from= renamed.map((d,_) -> disp(d.x())).toList();
    if (from.isEmpty()){ return Optional.empty(); }
    var many= from.size() > 1;
    return Optional.of("Generic type parameter"+(many ? "s " : " ")+and(from)+" of "+parentSig
      +(many ? " are named " : " is named ")+and(renamed.map((_,h) -> disp(h.x())).toList())+" here.");
  }
  private static String and(List<String> xs){
    if (xs.size() == 1){ return xs.getFirst(); }
    return Join.of(xs.subList(0, xs.size()-1), "", ", ", "")+" and "+xs.getLast();
  }
  String expRepr(E toErr){ return switch (toErr){
    case Call c -> "method call "+methodSig(c.name());
    case X x -> "parameter "+disp(x.src().inner instanceof fearlessFullGrammar.E.Implicit ? "::" : x.name());
    case Literal l -> l.thisName().equals("this")
      ? "type declaration "+tNameADisp(l.name())
      : "object literal "+bestNameNoRc(l);
    case Type(var t, _) -> "object literal instance of "+typeRepr(true, t.withRC(RC.imm));
    };}
  String expReprDirect(boolean skipImm, E toErr){ return switch (toErr){
    case Literal l -> bestNamePkg0(false, bestLitName(false, skipImm, l));
    case Type(var t, _) -> typeRepr(skipImm, t);
    default -> throw Bug.unreachable();
    };}
  String expRepr(inference.E toErr){ return switch (toErr){
    case inference.E.Call c -> "method call "+methodSig(c.name());
    case inference.E.X(var name, _, _, _) -> "parameter "+disp(name);
    case inference.E.Literal l -> l.thisName().equals("this")
      ? "type declaration "+tNameADisp(l.name())
      : l.infName() && l.cs().isEmpty() && !(l.t() instanceof inference.IT.RCC r && !r.c().name().equals(l.name())) ? "object literal "+disp(anonRepr)
      : "object literal "+bestNamePkg0(l.infName(), bestLitName(l));
    case inference.E.Type t -> "object literal instance of "+tNameADisp(t.type().c().name());
    };}
  String methodSig(MName m){ return methodSig("", m); }
  String methodSig(String pre, TName t, MName m){ return methodSig(pre+tNameA(t), m); }
  String methodSig(String pre, Literal l, MName m){ return methodSig(pre+bestLitName(true, true, l), m); }
  String methodSig(String pre, inference.E.Literal l, MName m){ return methodSig(pre+bestLitName(l), m); }
  static String methodSig(String pre, MName m){ return disp(Join.of(Collections.nCopies(m.arity(), "_"), pre+m.s()+"(", ",", ")", pre+m.s())); }
  public static boolean rcOnlyMismatch(T got, T req){
    return got.withRC(RC.imm).equals(req.withRC(RC.imm));
  }
  String text(){ return sb.toString().stripTrailing(); }
  public Err pTypeArgBounds(String first, String kindingTarget, String paramName, int index, T bad, String allowedStr, String gotStr){
    var badStr= typeRepr(false, bad);
    var e= line(first)
      .line("Generic type argument "+(index+1)+" ("+badStr+") does not satisfy the bounds")
      .line("for generic type parameter "+paramName+" in "+kindingTarget+".")
      .line("Here "+paramName+" can only use "+allowedStr+".");
    var capabilityHidden= bad instanceof T.X || bad instanceof T.ReadImmX;
    if (!capabilityHidden){ return e; }
    return e.line("But generic type argument "+badStr+" can only use "+gotStr+".");
  }

  Err line(String s){
    assert !s.isEmpty();
    assert sb.lastIndexOf("\n") == sb.length()-1;
    s = s.stripTrailing();
    sb.append(s).append("\n");
    return this;
  }
  Err blank(){
    var n= sb.length();
    assert sb.charAt(n-1) == '\n';
    var noBlankYet= n < 2 || sb.charAt(n-2) != '\n';
    if (noBlankYet){ sb.append('\n'); }
    return this;
  }
  Err list(String heading, List<String> items){
    assert !items.isEmpty();
    if (items.size() == 1){ return line(heading+": "+items.getFirst()+"."); }
    line(heading+":");
    items.forEach(this::bullet);
    return this;
  }
  Err didYouMean(List<String> options){
    assert !options.isEmpty();
    if (options.size() == 1){ return line("Did you mean "+options.getFirst()+" ?"); }
    line("Did you mean one of the following?");
    options.forEach(this::bullet);
    return this;
  }
  Err bullet(String s){
    assert !s.isBlank();
    return line("- "+s.stripTrailing().replace("\n", "\n  "));
  }
  Err pCallCantBeSatisfied(Literal d, Call c){
    return line("This call to method "+methodSig(c.rc().toStrSpace(), d, c.name())+" cannot typecheck.");
  }
  Err pCallCantBeSatisfied(Call c){
    return line("This call to method "+methodSig(c.name())+" cannot typecheck.");
  }
  Err pReceiverRequiredByPromotion(List<MType> promos){
    var byRc= promos.stream().collect(Collectors.groupingBy(MType::rc, LinkedHashMap::new, Collectors.mapping(MType::promotion, Collectors.toList())));
    if (byRc.size() <= 1){ return this; }
    blank().line("Receiver required by each promotion:");
    byRc.keySet().stream()
      .sorted()
      .forEach(rc -> bullet(disp(rc)+" ("+Join.of(byRc.get(rc).stream().distinct(), "", ", ", "")+")"));
    return this;
  }
  public String gotMsg(boolean skipImm, String label, List<T> got, T expected){
    return label+" has type "+Join.of(got.stream().map(t -> typeRepr(skipImm, t)), "", " or ", "")
      +" instead of a subtype of "+typeRepr(skipImm, expected)+".";
  }
  FearlessException ex(E e){ return ex(e, e); }
  FearlessException typeErr(){ return withNotes(Code.TypeError); }
  FearlessException ex(E footerE, E focus){ return ex(footerE, focus, List.of()); }
  FearlessException ex(E footerE, E focus, List<T> inferred){
    var ts= Push.of(inferred.stream().map(t -> typeRepr(true, t)).toList(), inferredTargs(focus)).stream().distinct().toList();
    if (footerE instanceof X || footerE instanceof Type || ts.isEmpty()){ return typeErr(); }
    var body= text();
    var cp= _cp.apply(true);
    var footer= cp.limit(footerE, focus, 120).stripTrailing();
    var what= ts.size() == 1 ? "type "+ts.getFirst()+" was" : "types "+Join.of(ts.stream(), "", " and ", "")+" were";
    var header= "See inferred typing context below for how "+what+" introduced"+(cp.omitted ? " (\"...\" marks omitted code):\n" : ":\n");
    return Code.TypeError.of(() -> withNotes(body)+"\n\n"+header+footer);
  }
  private List<String> inferredTargs(E e){
    if (!(e instanceof Call c)){ return List.of(); }
    var own= inferredTargs(c) ? c.targs().stream().map(t -> typeRepr(true, t)).toList() : List.<String>of();
    return Push.of(own, inferredTargs(c.e()));
  }
  static boolean inferredTargs(Call c){
    var written= c.src().inner instanceof fearlessFullGrammar.E.Call(_, _, var sq, _, _, _, _) && sq.filter(s -> !s.ts().isEmpty()).isPresent();
    return !c.targs().isEmpty() && !written;
  }
  FearlessException wf(){
    assert sb.length() != 0;
    return withNotes(Code.WellFormedness);
  }
  private String withNotes(String body){ return body+Join.of(notes.get().stream(), "\n\n", "\n", "", ""); }
  private FearlessException withNotes(Code code){
    var body= text();
    return code.of(() -> withNotes(body));
  }
}