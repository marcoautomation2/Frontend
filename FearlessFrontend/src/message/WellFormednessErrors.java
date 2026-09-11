package message;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Stream;

import core.B;
import core.FearlessException;
import core.LiteralDeclarations;
import core.MName;
import core.RC;
import core.TName;
import fearlessFullGrammar.FileFull;
import fearlessFullGrammar.T;
import fearlessFullGrammar.T.X;
import fearlessParser.Parser;
import inference.E;
import inference.IT;
import inference.M;
import inject.Methods.Agreement;
import metaParser.NameSuggester;
import metaParser.PrettyFileName;
import metaParser.Span;
import naming.FreshPrefix;
import tools.SourceOracle.Ref;
import utils.Bug;
import utils.Join;
import utils.Streams;

public record WellFormednessErrors(String pkgName){
  @SuppressWarnings("serial")
  public static class ErrToFetchContext extends RuntimeException{
    public ErrToFetchContext(IT.RCC c){this.c= c;} public IT.RCC c;
    }
  Err err(){ return new Err(y->y,x->x, trunk->new CompactPrinter(pkgName, Map.of(), trunk), new StringBuilder()); }

  public FearlessException notClean(Ref uri, FileFull f){
    var e= err()
      .line("Package directives outside of rank file.")
      .line("Only the rank file should not contain directives like maps and uses.")
      .blank()
      .line("Found non-empty:");
    boolean any= false;
    if (!f.maps().isEmpty()){ e.bullet("maps: " + previewList(f.maps(), 5)); any= true; }
    if (!f.uses().isEmpty()){ e.bullet("uses: " + previewList(f.uses(), 8)); any= true; }
    assert any;
    return e.wf().addSpan(new Span(uri.fearURI(),0,0,1,1));
  }

  private String previewList(List<?> c, int limit){
    StringBuilder sb= new StringBuilder();
    int i= 0;
    for (var x:c){
      if (i > 0){ sb.append(", "); }
      if (i == limit){
        sb.append("...").append(" (size=").append(c.size()).append(')');
        return sb.toString();
      }
      sb.append(String.valueOf(x));
      i++;
    }
    return sb.toString();
  }

  public FearlessException expectedSingleUriForPackage(List<Ref> heads, String pkgName){
    if (heads.isEmpty()){
      return badRank(err()
        .line("No rank file found for package "+Err.disp(pkgName)+".")
        .line("Each package must have exactly one source file whose name is their rank.")
        .line("in some folder inside the project folder."))
        .wf();
    }
    var e= err()
      .line("Ambiguous rank file for package "+Err.disp(pkgName)+".")
      .line("Found "+heads.size()+" files that look like rank head candidates:");
    heads.forEach(u->e.bullet(PrettyFileName.displayFileName(u.fearURI())));
    e.line("There must be exactly one source file whose name represents this package rank.")
     .line("Rename or remove the extra files so that only one file name is of form \"_rank_*.fear\".");
    return badRank(e).wf();
  }
  public FearlessException mapConflict(String target, String in, List<String> bests){
    int limit= 12;
    var e= err()
      .line("For package "+Err.disp(target)+", the virtual package name "+Err.disp(in)
           +" is mapped to different real packages:");
    bests.stream().limit(limit).forEach(e::line);
    if (bests.size() > limit){ e.line(" - ... ("+(bests.size()-limit)+" more)"); }
    e.blank()
     .line("These mappings come from rank files with the same priority (same rank),")
     .line("so there is no higher one to override the other.")
     .blank()
     .line("How mapping works:")
     .bullet("Each package rank file can have lines like: map 'virtual' as 'real' in 'target';")
     .bullet("If a virtual package name is never mentioned, it implicitly maps to itself (identity).")
     .bullet("Higher-rank packages override lower-rank ones.")
     .blank()
     .line("How to fix it:")
     .bullet("Decide which real package should represent "+Err.disp(in)+" inside of "+Err.disp(target)+".")
     .bullet("Add one mapping line in a higher-rank package (typically your top-level application"
            +" package), so that it overrides the conflicting ones.");
    return e.wf();
  }
  public Err badRank(Err err){
    return err
      .line("Every package must declare its rank: base, core, driver, worker, framework, accumulator, tool, or app.")
      .line("The rank file is the file whose name matches the rank name.")
      .blank()
      .line("For example, for an application you would typically have a file named")
      .line("  \"_rank_app.fear\"")
      .line("Other examples: \"_rank_driver.fear\", \"_rank_framework.fear\" or \"_rank_app175.fear\"; with explicit rank number.")
      .line("As a rule of thumb: final applications use appNNN; shared libraries often use workerNNN or frameworkNNN.");
  }

  public FearlessException usedDeclaredNameClash(String pkgName, Set<TName> names, Set<String> keySet){
    for (TName n:names){
      if (!keySet.contains(n.s())){ continue; }
      return err()
        .line("Name clash: name "+Err.disp(n.s())+" is declared in package "+Err.disp(pkgName)+".")
        .line("Name "+Err.disp(n.s())+" is also used in a \"use\" directive.")
        .wf()
        .addFrame("a type name", Parser.span(n.pos(), n.s().length()));
    }
    throw Bug.unreachable();
  }

  public FearlessException usedUndeclaredName(TName tn, String contextPkg, List<TName> scope, List<TName> all){
    return new UndeclaredNameContext(
      this::err,
      tn, contextPkg, scope, all,
      all.stream().map(TName::pkgName).filter(p->!p.isEmpty()).distinct().sorted().toList(),
      tn.pkgName(), tn.simpleName()
    ).build();
  }

  private record UndeclaredNameContext(
    Supplier<Err> err,
    TName tn, String contextPkg, List<TName> scope, List<TName> all,
    List<String> allPkgs, String typedPkg, String typedSimple
  ){
    FearlessException build(){
      return pkgDoesNotExist()
        .or(this::otherArity)
        .orElseGet(this::undeclaredInPkg);
    }

    private Optional<FearlessException> pkgDoesNotExist(){
      if (typedPkg.isEmpty()){ return Optional.empty(); }
      if (allPkgs.contains(typedPkg)){ return Optional.empty(); }
      var e= err.get().line("Package "+Err.disp(typedPkg)+" does not exist.");
      NameSuggester.suggest(typedPkg, allPkgs, (_,cs,best)->{
        best.ifPresent(b->e.line("Did you mean "+Err.disp(b)+" ?"));
        e.line(Join.of(cs.stream().map(Err::disp), "Visible packages: ", ", ", "."));
        return null;
      });
      return Optional.of(make(e));
    }

    private <A,R> List<R> userMap(Function<A,R> f, Stream<A> s){ return s.map(f).distinct().sorted().toList(); }

    private Optional<FearlessException> otherArity(){
      List<TName> candidates= typedPkg.isEmpty() ? scope : typesInPkg(typedPkg);
      var arities= userMap(TName::arity, candidates.stream().filter(t->t.simpleName().equals(typedSimple)));
      assert !arities.contains(tn.arity());
      if (arities.isEmpty()){ return Optional.empty(); }
      String targetPkg= typedPkg.isEmpty() ? contextPkg : typedPkg;

      var e= err.get()
        .line("Name "+Err.disp(typedSimple)+" is not declared with "+tn.arity()+" type parameter(s) in package "+Err.disp(targetPkg)+".")
        .line("Name "+Err.disp(typedSimple)+" is only declared with "
          +(arities.size() == 1
            ? arities.getFirst()+" type parameter(s)."
            : Join.of(arities, "the following numbers of type parameters: ", ", ", ".")
          ))
        .line("Did you accidentally add or omit a type parameter?");
      return Optional.of(make(e));
    }

    private FearlessException undeclaredInPkg(){
      List<TName> inPkg= typedPkg.isEmpty() ? scope : typesInPkg(typedPkg);
      var simpleInPkg= simpleNames(inPkg);

      var e= err.get()
        .line("Type "+Err.disp(typedSimple)+" is not declared in package "+relevantPkgMsg()+".");
      var suggest= NameSuggester.suggest(typedSimple, simpleInPkg);
      if (!suggest.isEmpty()){ e.line(suggest); }

      if (!typedPkg.isEmpty()){ addOtherPkgNotePkgExplicit(e); return make(e); }

      var noBestLocal= NameSuggester.bestName(typedSimple, simpleInPkg).isEmpty();
      if (noBestLocal){ addOtherPkgNotePkgImplicit(e); }
      return make(e);
    }

    private String relevantPkgMsg(){
      if (!typedPkg.isEmpty()){ return Err.disp(typedPkg); }
      return Err.disp(contextPkg)+" and is not made visible via \"use\"";
    }

    private List<TName> typesInPkg(String pkg){ return all.stream().filter(t->t.pkgName().equals(pkg)).toList(); }
    private List<String> simpleNames(List<TName> xs){ return userMap(TName::simpleName, xs.stream()); }

    private void addOtherPkgNotePkgExplicit(Err e){
      var sameSimpleOther= userMap(TName::s, all.stream()
        .filter(t->!t.pkgName().equals(typedPkg))
        .filter(t->t.simpleName().equals(typedSimple)));
      addOptionsList(sameSimpleOther, e);
    }

    private void addOtherPkgNotePkgImplicit(Err e){
      var other= all.stream().filter(t->!t.pkgName().equals(contextPkg)).toList();
      if (other.isEmpty()){ return; }
      var simpleCandidates= userMap(TName::simpleName, other.stream());
      NameSuggester.bestName(typedSimple, simpleCandidates).ifPresent(bestSimple->
        addOptionsList(userMap(TName::s, all.stream().filter(t->t.simpleName().equals(bestSimple))), e));
    }

    private static String addUse= "Add a \"use\" or write the fully qualified name.";

    void addOptionsList(List<String> ss, Err e){
      if (ss.isEmpty()){ return; }
      e.line(Join.of(ss.stream().map(Err::disp), "Did you mean ", " or ", " ?"))
       .line(addUse);
    }

    private FearlessException make(Err e){
      return e.wf().addFrame("a type name", at());
    }

    private Span at(){ return Parser.span(tn.pos(), tn.s().length()); }
  }

  public FearlessException unknownUseHead(TName tn){
    var at= Parser.span(tn.pos(), tn.s().length());
    return err()
      .line("\"use\" directive refers to undeclared name: type "+Err.disp(tn.simpleName())
        +" is not declared in package "+Err.disp(tn.pkgName())+".")
      .wf()
      .addFrame("package header", at);
  }

  public FearlessException genericTypeVariableShadowTName(String pkgName, Map<TName, Set<X>> allXs, List<String> allNames, Set<String> use){
    var mergeAllXs= allXs.values().stream().flatMap(Set::stream).toList();
    for (var n:mergeAllXs){
      var clashDec= allNames.contains(n.name());
      var clashUse= use.contains(n.name());
      if (clashDec || clashUse){ return shadowMsg(pkgName, n, clashUse); }
    }
    throw Bug.unreachable();
  }

  private FearlessException shadowMsg(String pkgName, T.X n, boolean use){
    return err()
      .line("Type parameter "+Err.disp(n.name())+" is declared in package "+Err.disp(pkgName)+".")
      .line("Name "+Err.disp(n.name())+" is also used "+(use ? "in a \"use\" directive." : "as a type name."))
      .wf()
      .addFrame("a type name", n.span().inner);
  }

  public FearlessException duplicatedBound(List<RC> es, T.X n){
    RC dup= es.stream()
      .filter(e->es.stream().filter(ei->ei.equals(e)).count() > 1)
      .findFirst().get();
    return err()
      .line("Duplicate reference capability in the type parameter "+Err.disp(n.name())+".")
      .line("Reference capability "+Err.disp(dup.name())+" is repeated.")
      .wf()
      .addSpan(n.span().inner);
  }

  public FearlessException duplicatedName(TName name){
    return err()
      .line("Duplicate type declaration for "+err().tNameADisp(name)+".")
      .wf()
      .addFrame("a type name", Parser.span(name.pos(), name.s().length()));
  }

  public FearlessException circularImplements(Map<TName,E.Literal> rem){
    TName name= findCycleNode(rem);
    return err()
      .line("Circular implementation relation found involving "+err().tNameADisp(name)+".")
      .wf()
      .addFrame("type declarations", Parser.span(name.pos(), name.s().length()));
  }

  private TName findCycleNode(Map<TName,E.Literal> rem){
    var color= new HashMap<TName,Integer>(rem.size());
    for (var k:rem.keySet()){
      var hit= dfs(rem, k, color);
      if (hit != null){ return hit; }
    }
    throw Bug.unreachable();
  }

  private TName dfs(Map<TName,E.Literal> rem, TName u, Map<TName,Integer> color){
    Integer cu= color.get(u);
    if (cu != null){ return cu == 1 ? u : null; }
    color.put(u, 1);
    for (var c:rem.get(u).cs()){
      if (!rem.containsKey(c.name())){ continue; }
      var hit= dfs(rem, c.name(), color);
      if (hit != null){ return hit; }
    }
    color.put(u, 2);
    return null;
  }
  public FearlessException noSourceToInferFrom(E.Literal origin, M m){
    var empty= m.sig().m().isEmpty();
    var size= m.sig().ts().size();
    if (empty){
      return err()
        .line("Cannot infer signature and name for a method with "+size+" parameters.")
        .line("No supertype has a method with "+size+" parameters.")
        .wf()
        .addSpan(m.sig().span().inner)
        .addFrame(err().expRepr(origin), origin.span().inner);
    }
    var name= err().methodSig(m.sig().m().get());
    var allParHasType= m.sig().ts().stream().allMatch(Optional::isPresent);
    var argsPresentNoTypes= size > 0 && !allParHasType;
    if (argsPresentNoTypes){
      return err()
        .line("Cannot infer signature of method "+name+".")
        .line("No supertype has a method named "+name+" with "+size+" parameters.")
        .wf()
        .addSpan(m.sig().span().inner)
        .addFrame(err().expRepr(origin), origin.span().inner);
    }
    var e= err()
      .line("Missing return type for method "+name+".")
      .line("Add an explicit return type before '->'.");
    if (allParHasType){
      e = e
        .line("Alternatively (less common), if you intended to override and omit the signature,")
        .line("the signature must be inherited from a supertype.");
    } else { // size == 0
      e = e
        .line("If you intended to override and omit the signature,")
        .line("the signature must be inherited from a supertype.");
    }
    return e
      .line("Cannot infer signature of method "+name+".")
      .line("No supertype has a method named "+name+" with "+size+" parameters.")
      .wf()
      .addSpan(m.sig().span().inner)
      .addFrame(err().expRepr(origin), origin.span().inner);
  }
  public String retTypeDisagreement(){ return "Return type disagreement"; }
  public String argTypeDisagreement(int i){ return "Type disagreement about argument "+i; }

  public FearlessException noAgreement(Agreement at, FreshPrefix fresh, List<?> res, String msg){
    var rc=at.rc().map(r->r.toStrSpace(false)).orElse("");
    var e= err()
      .line(msg+" for method "+err().methodSig(rc,at.mName())+" with "+at.mName().arity()+" parameters.")
      .line(Join.of(
        res.stream().map(o->{//Can be RC or inference.IT.RCC
          if (o instanceof inference.IT.RCC rcc){ return err().typeRepr(rcc); }
          return Err.disp(o);
        }),
        "Different options are present in the implemented types: ", ", ", "."
      ))
      .line(Err.up(err().expRepr(at.lit()))+" must declare a method "
        +err().methodSig(at.mName())+" explicitly choosing the desired option.");
    return e.wf().addFrame(err().expRepr(at.lit()), at.span());
  }

  public FearlessException methodGenericArityDisagreementBetweenSupers(Agreement at, FreshPrefix fresh, List<List<B>> res){
    var e= err()
      .line("The number of type parameters disagrees for method "+err().methodSig(at.mName())
        +" with "+at.mName().arity()+" parameters.")
      .line(Join.of(res.stream().map(Err::disp), "Different options are present in the implemented types: ", ", ", "."))
      .line(Err.up(err().expRepr(at.lit()))+" cannot implement all of those types.");
    return e.wf().addFrame(err().expRepr(at.lit()), at.span());
  }

  public FearlessException methodGenericArityDisagreesWithSupers(Agreement at, FreshPrefix fresh, int userArity, int superArity, List<B> userBs, List<B> superBs){
    String sB= Err.disp(superBs.stream().map(b->new B("-", b.rcs())).toList());
    return err()
      .line("Invalid method implementation for "+err().methodSig(at.rc().orElse(RC.imm).toStrSpace(),at.lit(), at.mName())+".")
      .line("The method "+err().methodSig(at.mName())+" declares "+userArity+" type parameter(s), but supertypes declare "+superArity+".")
      .line("Local declaration: "+Err.disp(userBs)+".")
      .line("From supertypes: "+sB+".")
      .line("Change the local number of type parameters to "+superArity+", or adjust the supertypes.")
      .wf()
      .addFrame(err().expRepr(at.lit()), at.span());
  }

  public FearlessException methodBsDisagreementBetweenSupers(Agreement at, FreshPrefix fresh, List<List<B>> res){
    assert res.size() >= 2;
    int n= res.getFirst().size();
    assert res.stream().allMatch(bs->bs.size() == n);
    int i= firstRcsDisagreementIndex(res);

    String opts= Join.of(res.stream().map(bs->Err.disp(bs.get(i))).distinct().sorted(), "", " and ", ".");
    String m= err().methodSig(at.mName());

    return err()
      .line("Invalid method implementation for "+err().methodSig(at.rc().orElse(RC.imm).toStrSpace(),at.lit(), at.mName())+".")
      .line("Supertypes disagree on the capability bounds for type parameter "+(i+1)+" of "+m+".")
      .line("Type parameter names may differ across supertypes; only the position matters.")
      .line("Different supertypes declare: "+opts)
      .line(Err.up(err().expRepr(at.lit()))+" cannot implement all of those supertypes.")
      .line("Make the supertypes agree on these bounds, or remove one of the conflicting supertypes.")
      .wf()
      .addFrame(err().expRepr(at.lit()), at.span());
  }

  public FearlessException methodBsDisagreesWithSupers(Agreement at, FreshPrefix fresh, List<B> userBs, List<B> superBs){
    assert userBs.size() == superBs.size();
    int i= firstRcsDisagreementIndex(List.of(userBs, superBs));
    var u= userBs.get(i);
    var s= superBs.get(i);
    String m= err().methodSig(at.mName());
    String uB= Err.disp(u);
    String sB= Err.disp(new B("-", s.rcs()));

    return err()
      .line("Invalid method implementation for "+err().methodSig(at.rc().orElse(RC.imm).toStrSpace(),at.lit(), at.mName())+".")
      .line("The local declaration uses different capability bounds than the supertypes for type parameter "+(i+1)+" of "+m+".")
      .line("Local: "+uB+".")
      .line("From supertypes: "+sB+".")
      .line("The parameter name may differ; only the position matters.")
      .line("Change the local bounds to match the supertypes, or adjust the supertypes.")
      .wf()
      .addFrame(err().expRepr(at.lit()), at.span());
  }

  private int firstRcsDisagreementIndex(List<List<B>> res){
    return Streams.firstPos(res.getFirst(), i->{
        var r0= res.getFirst().get(i).rcs();
        return !res.stream().allMatch(bs->bs.get(i).rcs().equals(r0));
      }).get();
  }
  public FearlessException itTooDeep(E at,IT.RCC blame){
    return err()
      .line("Type "+err().typeRepr(blame))
      .line("grew incontrollably during inference.")
      .wf()
      .addFrame(err().expRepr(at), at.span().inner);
  }
  public FearlessException ambiguousImpl(E.Literal origin, FreshPrefix fresh, boolean abs, M m, List<inference.M.Sig> options){
    return err()
      .line("Cannot infer the name for a method with "+m.sig().ts().size()+" parameters.")
      .line("Many"+(abs ? " abstract" : "")+" methods with "+m.sig().ts().size()+" parameters could be selected:")
      .line(Join.of(
        options.stream().map(mi->Err.disp(mi.rc().get()+" "+mi.m().get().s())),
        "Candidates: ", ", ", "."
      ))
      .wf()
      .addSpan(m.sig().span().inner)
      .addFrame(err().expRepr(origin), origin.span().inner);
  }

  public FearlessException ambiguousImplementationFor(List<M.Sig> ss, List<TName> options, Agreement at, FreshPrefix fresh){
    return err()
      .line("Ambiguous implementation for method "+Err.disp(at.mName().s())+" with "+at.mName().arity()+" parameters.")
      .line("Different options are present in the implemented types:")
      .line(Join.of(options.stream().map(err()::tNameADisp), "Candidates: ", ", ", "."))
      .line(Err.up(err().expRepr(at.lit()))+" must declare a method "+Err.disp(at.mName().s())
        +" explicitly implementing the desired behaviour.")
      .wf()
      .addFrame(err().expRepr(at.lit()), at.span());
  }

  public FearlessException multipleWidenTo(E.Literal owner, List<IT.C> widen){
    var e= err()
      .line(err().expRepr(owner)+" implements \"base.WidenTo[_]\" more than once.")
      .line("At most one \"base.WidenTo[_]\" supertype is allowed, because it defines the preferred widened type.")
      .blank()
      .line("Found the following base.WidenTo supertypes:");
    widen.forEach(c->e.bullet(Err.disp(c.toString())));
    return e.wf().addFrame(err().expRepr(owner), owner.span().inner);
  }
  public FearlessException duplicatedNamedLiteral(E.Literal owner,M m, E.Literal in){
    String ctx= Err.up(err().expRepr(owner));
    return err()
      .line(ctx+" implements method "+err().methodSig(m.sig().m().get())+".")
      .line("The body of method "+err().methodSig("",owner,m.sig().m().get())+" needs to be duplicated to satisfy multiple RC overloads from the supertypes.")
      .line("However, it contains "+err().expRepr(in)+".")
      .line("Object literals with their own unique explicit type cannot be duplicated.")
      .wf()
      .addFrame(err().expRepr(owner), owner.span().inner);
  }

  public FearlessException baseIdNotOnlyHash(E.Literal owner){
    String ctx= Err.up(err().expRepr(owner));
    return err()
      .line(ctx+" implements "+err().tNameADisp(LiteralDeclarations.baseId)+".")
      .line("Only the method "+err().methodSig(new MName("#",1))+" can be declared here.")
      .wf()
      .addFrame(err().expRepr(owner), owner.span().inner);
  }
  public FearlessException extendedSealed(E.Literal owner, FreshPrefix fresh, TName isSealed){
    String ownerPkg= owner.name().pkgName();
    String sealedPkg= isSealed.pkgName();
    assert !ownerPkg.equals(sealedPkg);

    String ctx= Err.up(err().expRepr(owner));
    return err()
      .line(ctx+" implements sealed type "+err().tNameADisp(isSealed)+".")
      .line("Sealed types can only be implemented in their own package.")
      .line(ctx+" is defined in package "+Err.disp(ownerPkg)+".")
      .line("Type "+Err.disp(isSealed.simpleName())+" is defined in package "+Err.disp(sealedPkg)+".")
      .wf()
      .addFrame(err().expRepr(owner), owner.span().inner);
  }
  public FearlessException intLiteralOutOfRange(TName lit){
    BigInteger v= LiteralDeclarations.intLiteralBig(lit.simpleName());
    return err()
      .line("Integer literal is out of range for \"base.Int\".")
      .line("\"base.Int\" must be representable as a 64-bit signed integer.")
      .line("Valid range: "+LiteralDeclarations.intMin+" .."+LiteralDeclarations.intMax+".")
      .line("This literal is: "+Err.disp(v)+".")
      .line("Hint: if you need arbitrary precision numbers, use \"base.Num\".")
      .wf().addSpan(lit.approxSpan().inner);
  }
  public FearlessException natLiteralOutOfRange(TName lit){
    BigInteger v= LiteralDeclarations.natLiteralBig(lit.simpleName());
    return err()
      .line("Natural literal is out of range for \"base.Nat\".")
      .line("\"base.Nat\" must be representable as a 64-bit unsigned integer.")
      .line("Valid range: "+LiteralDeclarations.natMin+" .."+LiteralDeclarations.natMax+".")
      .line("This literal is: "+Err.disp(v)+".")
      .line("Hint: if you need arbitrary precision numbers, use \"base.Num\".")
      .wf().addSpan(lit.approxSpan().inner);
  }
  public FearlessException floatLiteralNotExactlyRepresentable(TName lit){
    String raw= lit.simpleName();
    double d= LiteralDeclarations.floatLiteralDouble(raw);
    double nearD= Double.isFinite(d) ? d : Math.copySign(Double.MAX_VALUE,d);
    String near= LiteralDeclarations.floatExactFearlessLit(nearD);
    var e= err()
      .line("Float literal is not exactly representable as \"base.Float\".")
      .line("\"base.Float\" must be representable exactly as a 64-bit IEEE 754 double.")
      .line("This literal is: "+raw+".");
    if (!Double.isFinite(d)){ e.line("This literal overflows; the nearest representable value is "+Err.disp(near)+"."); }
    else{
      e.line("If rounded, the nearest representable value is "+Err.disp(near)+".")
       .line("Write "+Err.disp(raw+LiteralDeclarations.softSuffix)+" to accept that rounding.")
       .line("Hint: if you need arbitrary precision numbers, use \"base.Num\".");
    }
    return e.wf().addSpan(lit.approxSpan().inner);
  }
}