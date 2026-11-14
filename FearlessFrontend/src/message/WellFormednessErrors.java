package message;

import static message.Err.*;

import java.math.BigInteger;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.B;
import core.FearlessException;
import core.LiteralDeclarations;
import core.MName;
import core.RC;
import core.TName;
import core.TSpan;
import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.FileFull;
import fearlessFullGrammar.T;
import fearlessFullGrammar.T.X;
import inference.E;
import inference.IT;
import inference.M;
import inject.Methods.Agreement;
import inject.TypeRename;
import metaParser.NameSuggester;
import metaParser.PrettyFileName;
import metaParser.Span;
import pkgmerge.Package;
import tools.Fs;
import tools.SourceOracle.Ref;
import typeSystem.Kinding;
import utils.Join;
import utils.Pos;
import java.util.EnumSet;
import utils.Push;

public record WellFormednessErrors(String pkgName, Map<String,String> map, Map<String,String> writtenIn, LinkedHashSet<String> printed){
  public WellFormednessErrors(String pkgName){ this(pkgName, Map.of(), Map.of(), new LinkedHashSet<>()); }
  Err err(){ return err(List.of()); }
  private Err err(List<String> steps){ return err(y -> y, x -> x, _ -> null, steps); }
  Err err(Function<core.T.C,core.T.C> publicHead, Function<TName,TName> preferredForFresh, Function<TName,core.E.Literal> decs, List<String> steps){
    var written= written(map);
    return new Err(publicHead, preferredForFresh, decs, trunk -> new CompactPrinter(pkgName, written, trunk ? _ -> {} : printed::add, trunk), () -> notes(written, steps), new StringBuilder());
  }
  private List<String> notes(Map<String,String> written, List<String> steps){ return Stream.concat(steps.stream(), printed.stream().flatMap(n -> note(written, n))).distinct().sorted(nameFirst).toList(); }
  public static Map<String,String> written(Map<String,String> map){
    return map.entrySet().stream().collect(Collectors.toUnmodifiableMap(Map.Entry::getValue, Map.Entry::getKey));
  }
  private static final Comparator<String> nameFirst= Comparator.comparing(s -> !s.startsWith("Name "));
  private Stream<String> note(Map<String,String> written, String n){
    var dot= TName.pkgDot(n);
    var out= n.substring(0, dot);
    var in= written.get(out);
    var w= in+n.substring(dot);
    return Stream.concat(Optional.ofNullable(written.get(n)).map(a -> standsFor(a, w, "use "+w+" as "+a)).stream(), Stream.of(refersTo(pkgName, in, out, writtenIn)));
  }
  public static List<String> resolution(Package p, String written){
    var dot= TName.pkgDot(written);
    if (dot != -1){ return pkgMapped(p.name(), written.substring(0, dot), p.map(), p.writtenIn()); }
    return p.uses().stream()
      .filter(u -> u.out().equals(written))
      .flatMap(u -> Push.of(standsFor(written, u.in().s(), u), resolution(p, u.in().s())).stream())
      .toList();
  }
  private static List<String> pkgMapped(String target, String in, Map<String,String> map, Map<String,String> writtenIn){
    var out= map.get(in);
    if (out == null){ return List.of(); }
    return List.of(refersTo(target, in, out, writtenIn));
  }
  private static String refersTo(String target, String in, String out, Map<String,String> writtenIn){
    var m= new FileFull.Map(in, out, target, List.of(), Pos.unknown);
    return inFolders(target)+" uses package name "+disp(in)+" to refer to the code inside folders named "+disp("_"+out)+", because of "+disp(m)+", written in "+Objects.requireNonNull(writtenIn.get(in))+".";
  }
  private static String inFolders(String pkg){ return "Source code inside folders named "+disp("_"+pkg); }
  private static String standsFor(String from, String to, Object directive){
    return "Name "+disp(from)+" stands for "+disp(to)+" because of "+disp(directive)+".";
  }
  private FearlessException wf(Err e, E at){ return e.wf().addFrame(err().expRepr(at), at.span().inner); }
  private FearlessException wf(Err e, Agreement at){ return e.wf().addFrame(err().expRepr(at.lit()), at.span()); }
  private FearlessException wf(Err e, M.Sig s, E.Literal origin){ return e.wf().addSpan(s.span().inner).addFrame(err().expRepr(origin), origin.span().inner); }
  private FearlessException wfUse(Err e, TName tn){ return e.wf().addFrame("package header", TSpan.fromPos(tn.pos(), tn.s().length()).inner); }
  private Err invalidMethImpl(Agreement at){ return err().line("Invalid method implementation for "+err().methodSig(at.rc().orElse(RC.imm).toStrSpace(), at.lit(), at.mName())+"."); }
  public FearlessException notClean(FileFull f){
    var e= err()
      .line("Package directives outside of rank file.")
      .line("Only the rank file can contain directives like maps and uses.")
      .blank()
      .line("Found non-empty:");
    assert !f.noDirectives();
    if (!f.maps().isEmpty()){ e.bullet("maps: "+previewList(f.maps(), 5)); }
    if (!f.uses().isEmpty()){ e.bullet("uses: "+previewList(f.uses(), 8)); }
    var first= Stream.concat(
        f.maps().stream().map(m -> TSpan.fromPos(m.pos(), m.in().length()).inner),
        f.uses().stream().map(u -> TSpan.fromPos(u.in().pos(), u.in().s().length()).inner))
      .min(Comparator.comparingInt(Span::startLine).thenComparingInt(Span::startCol)).orElseThrow();
    return e.wf().addSpan(first);
  }
  private String previewList(List<?> c, int limit){
    var shown= Join.of(c.stream().limit(limit), "", ", ", "", "");
    return c.size() <= limit ? shown : shown+", ... (size="+c.size()+")";
  }
  public FearlessException expectedSingleUriForPackage(List<Ref> heads){
    if (heads.isEmpty()){
      return badRank(err()
        .line("No rank file found for package "+disp(pkgName)+".")
        .line("Each package must have exactly one source file whose name is its rank,")
        .line("in some folder inside the project folder."))
        .wf();
    }
    var e= err()
      .line("Ambiguous rank file for package "+disp(pkgName)+".")
      .line("Found "+heads.size()+" files that look like rank head candidates:");
    heads.forEach(u -> e.bullet(PrettyFileName.displayFileName(u.fearURI())));
    e.line("There must be exactly one source file whose name represents this package rank.")
     .line("Rename or remove the extra files so that only one file name is of form \"_rank_*.fear\".");
    return badRank(e).wf();
  }
  public FearlessException mapConflict(String in, List<String> bests){
    var limit= 12;
    var e= err()
      .line("Maps of the same rank give package name "+disp(in)+" different folders, for source code inside folders named "+disp("_"+pkgName)+":");
    bests.stream().limit(limit).forEach(e::line);
    if (bests.size() > limit){ e.line("- ... ("+(bests.size()-limit)+" more)"); }
    e.blank()
     .line("How maps work:")
     .bullet("A rank file can have lines like \"map name as _folder in _target;\".")
     .bullet("With no map, package name \"x\" refers to the code inside folders named \"_x\".")
     .bullet("A map in a rank file of higher rank overrides the maps of lower rank, and lists their folders with \"instead of\".")
     .blank()
     .line("How to fix it:")
     .bullet("Decide which folder package name "+disp(in)+" refers to, for source code inside folders named "+disp("_"+pkgName)+".")
     .bullet("Add one map in a rank file of higher rank (typically the rank file of your application"
            +"), with \"instead of\" listing every folder chosen by the maps of lower rank.");
    return e.wf();
  }
  public FearlessException mapToMissingFolder(String role, String folder, String directive, List<String> pkgs){
    var e= err().line("The map "+role+" folders named "+disp("_"+folder)+", but no folder is named "+disp("_"+folder)+":").line(directive);
    NameSuggester.suggest(folder, pkgs, (_,_,best) -> { best.ifPresent(b -> e.line("Did you mean "+disp("_"+b)+" ?")); return null; });
    return e.line(Join.of(pkgs.stream().map(p -> disp("_"+p)), "Existing folders: ", ", ", ".")).wf();
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
  public FearlessException usedDeclaredNameClash(Set<TName> names, Set<String> keySet){
    var n= names.stream().filter(x -> keySet.contains(x.s())).findFirst().get();
    return err()
      .line("Name clash: name "+disp(n.s())+" is declared in package "+disp(pkgName)+".")
      .line("Name "+disp(n.s())+" is also used in a \"use\" directive.")
      .wf()
      .addFrame("a type name", n.approxSpan().inner);
  }
  public FearlessException usedUndeclaredName(TName written, TName resolved, List<TName> scope, List<TName> all, Map<String,Ref> ranks, List<String> steps){
    var pkg= resolved.pkgName();
    var notLower= ranks.containsKey(pkg) && !pkg.equals(pkgName) && all.stream().noneMatch(t -> t.pkgName().equals(pkg));
    if (notLower){ return typeName(ranks(err().line("The type name "+disp(written.s())+" refers to "+notLower(pkg, rankName(ranks.get(pkg)).equals(rankName(ranks.get(pkgName))))+"."), pkg, ranks.get(pkgName), ranks.get(pkg)), written); }
    Function<TName,String> shown= t -> err().cp().t.ofFull(t.withoutPkgName().withPkgName(map.getOrDefault(t.pkgName(), t.pkgName())));
    return new UndeclaredNameContext(
      () -> err(steps),
      written, pkgName, scope, all, shown, this::aliasShown,
      all.stream().map(TName::pkgName).filter(p -> !p.isEmpty()).distinct().sorted().toList(),
      resolved.pkgName(), resolved.simpleName()
    ).build();
  }
  private String aliasShown(String s){
    Optional.ofNullable(map.get(s)).ifPresent(r -> err().cp().t.ofFull(new TName(r, 0, Pos.unknown)));
    return s;
  }
  private record UndeclaredNameContext(
    Supplier<Err> err,
    TName tn, String contextPkg, List<TName> scope, List<TName> all, Function<TName,String> display, Function<String,String> simpleShown,
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
      return Optional.of(typeName(missingPkg(err.get(), contextPkg, typedPkg, allPkgs, Optional.empty()), tn));
    }
    private <A,R> List<R> userMap(Function<A,R> f, Stream<A> s){ return s.map(f).distinct().sorted().toList(); }
    private List<String> shownInOrder(Stream<TName> s){ return s.sorted(Comparator.comparing(TName::s)).map(display).distinct().toList(); }
    private Optional<FearlessException> otherArity(){
      var candidates= typedPkg.isEmpty() ? scope : typesInPkg(typedPkg);
      var arities= userMap(TName::arity, candidates.stream().filter(t -> t.simpleName().equals(typedSimple)));
      assert !arities.contains(tn.arity());
      if (arities.isEmpty()){ return Optional.empty(); }
      var targetPkg= typedPkg.isEmpty() ? contextPkg : typedPkg;
      var e= err.get()
        .line("Name "+disp(typedSimple)+" is not declared with "+count(tn.arity(), "generic type parameter")+" in package "+disp(targetPkg)+".")
        .line("Name "+disp(typedSimple)+" is only declared with "
          +(arities.size() == 1
            ? count(arities.getFirst(), "generic type parameter")+"."
            : "other numbers of generic type parameters.\n"+Join.of(arities.stream().map(n -> disp(typedSimple+genArity(n))), "Candidates: ", ", ", ".")
          ))
        .line("Did you accidentally add or omit a generic type argument?");
      return Optional.of(typeName(e, tn));
    }
    private FearlessException undeclaredInPkg(){
      var e= err.get()
        .line("Type "+disp(typedSimple)+" is not declared in package "+relevantPkgMsg()+".");
      if (!typedPkg.isEmpty()){
        NameSuggester.suggest(typedPkg+"."+typedSimple, userMap(TName::s, typesInPkg(typedPkg).stream()), (_,cs,best) -> inScope(e, cs, best, c -> display.apply(new TName(c, 0, Pos.unknown))));
        addOtherPkgNotePkgExplicit(e);
        return typeName(e, tn);
      }
      var simpleInPkg= userMap(TName::simpleName, scope.stream());
      NameSuggester.suggest(typedSimple, simpleInPkg, (_,cs,best) -> inScope(e, cs, best, simpleShown));
      var noBestLocal= NameSuggester.bestName(typedSimple, simpleInPkg).isEmpty();
      if (noBestLocal){ addOtherPkgNotePkgImplicit(e); }
      return typeName(e, tn);
    }
    private String relevantPkgMsg(){
      if (!typedPkg.isEmpty()){ return disp(typedPkg); }
      return disp(contextPkg)+" and is not made visible via \"use\"";
    }
    private List<TName> typesInPkg(String pkg){ return all.stream().filter(t -> t.pkgName().equals(pkg)).toList(); }
    private void addOtherPkgNotePkgExplicit(Err e){
      var sameSimpleOther= shownInOrder(all.stream()
        .filter(t -> !t.pkgName().equals(typedPkg))
        .filter(t -> t.simpleName().equals(typedSimple)));
      addOptionsList(sameSimpleOther, e);
    }
    private void addOtherPkgNotePkgImplicit(Err e){
      var other= all.stream().filter(t -> !t.pkgName().equals(contextPkg)).toList();
      if (other.isEmpty()){ return; }
      var simpleCandidates= userMap(TName::simpleName, other.stream());
      NameSuggester.bestName(typedSimple, simpleCandidates).ifPresent(bestSimple ->
        addOptionsList(shownInOrder(all.stream().filter(t -> t.simpleName().equals(bestSimple))), e));
    }
    private static Void inScope(Err e, List<String> cs, Optional<String> best, Function<String,String> shown){
      best.ifPresent(b -> e.line("Did you mean "+disp(shown.apply(b))+" ?"));
      if (cs.size() <= 12){ e.line(Join.of(cs.stream().map(c -> disp(shown.apply(c))).distinct(), "In scope: ", ", ", ".")); }
      return null;
    }
    private static final String addUse= "Add a \"use\" or write the full type name.";
    void addOptionsList(List<String> ss, Err e){
      if (ss.isEmpty()){ return; }
      e.line(Join.of(ss.stream().map(Err::disp), "Did you mean ", " or ", " ?"));
      if (ss.stream().anyMatch(s -> s.contains("."))){ e.line(addUse); }
    }
  }
  public FearlessException useNotFullyQualified(TName tn){
    return wfUse(err()
      .line("\"use\" directive refers to "+disp(tn.s())+", which is not a full type name.")
      .line("A \"use\" directive refers to a type of another package by its full type name, as in \"use base.Str as Str;\"."), tn);
  }
  public FearlessException useOfTheCurrentPackage(TName tn){
    return wfUse(err()
      .line("\"use\" directive refers to type "+disp(tn.simpleName())+" declared inside folders named "+disp("_"+pkgName)+".")
      .line("A \"use\" directive can only refer to types declared in other folders.")
      .line(inFolders(pkgName)+" uses the simple names of its own types."), tn);
  }
  public FearlessException mapToATargetOfAnotherMap(String out, List<String> directives){
    var e= err().line(inFolders(pkgName)+" can use only one package name to refer to the code inside folders named "+disp("_"+out)+":");
    directives.forEach(e::line);
    return e.wf();
  }
  public FearlessException mapInBase(String directive){
    return mapErr("A map cannot apply to source code inside folders named "+disp("_base"), directive).wf();
  }
  private Err mapErr(String head, String directive){ return err().line(head+":").line(directive); }
  public FearlessException mapOfAnExistingPackage(String in, String directive){
    return mapErr("A map cannot give package name "+disp(in)+", because folders named "+disp("_"+in)+" exist", directive)
      .line("With no map, package name "+disp(in)+" refers to the code inside folders named "+disp("_"+in)+".").wf();
  }
  public FearlessException mapToItself(String directive){
    return mapErr("A map cannot refer to the code inside folders named "+disp("_"+pkgName)+" for source code inside folders named "+disp("_"+pkgName), directive)
      .line(inFolders(pkgName)+" uses the simple names of its own types.").wf();
  }
  private String notLower(String out, boolean sameRank){ return "the code inside folders named "+disp("_"+out)+", which has "+(sameRank ? "the same rank as" : "a higher rank than")+" the code inside folders named "+disp("_"+pkgName); }
  private Err ranks(Err e, String out, Ref rank, Ref otherRank){ return e.line("Folders named "+disp("_"+pkgName)+" have rank "+rankDisp(rank)+" and folders named "+disp("_"+out)+" have rank "+rankDisp(otherRank)+".").line("Source code can only refer to code of a lower rank."); }
  public FearlessException mapToNotLowerRank(String out, String directive, Ref rank, Ref otherRank, boolean sameRank){
    return ranks(mapErr("The map refers to "+notLower(out, sameRank), directive), out, rank, otherRank).wf();
  }
  public FearlessException insteadOfMismatch(String directive, List<String> overridden, FileFull.Map expected){
    var e= mapErr("The \"instead of\" list of a map must name exactly the folders chosen by the maps of lower rank that the map overrides", directive);
    e.line(overridden.isEmpty() ? "No map of lower rank chooses another folder." : "These maps of lower rank choose other folders:");
    overridden.forEach(e::line);
    return e.line("Expected: "+disp(expected+";")+".").wf();
  }
  private static Err missingPkg(Err e, String ctx, String pkg, List<String> visible, Optional<String> known){
    e.line(inFolders(ctx)+" cannot use package name "+disp(pkg)+".");
    var vs= visible.stream().filter(p -> !p.equals(ctx)).toList();
    known.or(() -> vs.isEmpty() ? Optional.empty() : NameSuggester.suggest(pkg, vs, (_,_,b) -> b)).ifPresent(b -> e.line("Did you mean "+disp(b)+" ?"));
    if (!vs.isEmpty()){ e.line(Join.of(vs.stream().map(Err::disp), "Visible package names: ", ", ", ".")); }
    return e;
  }
  public FearlessException useOfMissingPackage(TName tn, List<String> visible){ return wfUse(missingPkg(err(), pkgName, tn.pkgName(), visible, Optional.empty()), tn); }
  public FearlessException useOfAMapTarget(TName tn, String in, List<String> visible){ return wfUse(mappedAway(tn.pkgName(), in, visible), tn); }
  public FearlessException typeOfAMapTarget(TName tn, List<String> visible){ return typeName(mappedAway(tn.pkgName(), written(map).get(tn.pkgName()), visible), tn); }
  private Err mappedAway(String out, String in, List<String> visible){ return missingPkg(err(), pkgName, out, visible, Optional.of(in)).line(refersTo(pkgName, in, out, writtenIn)); }
  public FearlessException typeOfTheCurrentPackageQualified(TName tn, List<TName> options){
    var e= fullNameInvalid(err(), tn).line(inFolders(pkgName)+" uses the simple name "+disp(tn.simpleName())+" to refer to "+disp(tn.s())+".");
    if (!options.isEmpty()){ e.line(Join.of(options.stream().map(o -> disp(err().cp().t.ofFull(o))).distinct(), "Did you mean ", " or ", " ?")); }
    return typeName(e, tn);
  }
  public FearlessException typeWithAnAlias(TName tn, FileFull.Use u){
    return typeName(fullNameInvalid(err(pkgMapped(pkgName, tn.pkgName(), map, writtenIn)), tn).line(inFolders(pkgName)+" uses the simple name "+disp(u.out())+" to refer to "+disp(tn.s())+", because of "+disp(u)+"."), tn);
  }
  private Err fullNameInvalid(Err e, TName tn){ return e.line("The full type name "+disp(tn.s())+" is invalid in source code inside folders named "+disp("_"+pkgName)+"."); }
  private static FearlessException typeName(Err e, TName tn){ return e.wf().addFrame("a type name", TSpan.fromPos(tn.pos(), tn.s().length()).inner); }
  public FearlessException unknownUseHead(TName tn, Map<String,String> directives){
    return wfUse(err(pkgMapped(pkgName, tn.pkgName(), directives, writtenIn))
      .line("\"use\" directive refers to type "+disp(tn.simpleName())+", which is not declared in package "+disp(tn.pkgName())+"."), tn);
  }
  public FearlessException useOfNotLowerRank(TName tn, String pkg, Ref rank, Ref otherRank, boolean sameRank){
    return wfUse(ranks(err().line("\"use\" directive refers to "+notLower(pkg, sameRank)+"."), pkg, rank, otherRank), tn);
  }
  private static String rankName(Ref rank){
    var name= Fs.fileNameWithoutExtension(rank.fearPath()).substring("_rank_".length());
    return Character.isDigit(name.charAt(name.length()-1)) ? name : name+"999";
  }
  private static String rankDisp(Ref rank){ return disp(rankName(rank))+" ("+disp(Fs.fileNameWithExtension(rank.fearPath()))+")"; }
  public FearlessException genericTypeVariableShadowTName(Map<TName,Set<X>> allXs, List<String> allNames, Set<String> use){
    var n= allXs.values().stream().flatMap(Set::stream)
      .filter(x -> allNames.contains(x.name()) || use.contains(x.name()))
      .findFirst().get();
    return err()
      .line("Generic type parameter "+disp(n.name())+" is declared in package "+disp(pkgName)+".")
      .line("Name "+disp(n.name())+" is also used "+(use.contains(n.name()) ? "in a \"use\" directive." : "as a type name."))
      .wf()
      .addFrame("a type name", n.span().inner);
  }
  public FearlessException duplicatedBound(List<RC> es, T.X n){
    var dup= redeclaredElement(es);
    return err()
      .line("Duplicate reference capability in the generic type parameter "+disp(n.name())+".")
      .line("Reference capability "+disp(dup.name())+" is repeated.")
      .wf()
      .addSpan(n.span().inner);
  }
  public FearlessException duplicatedSupertype(Declaration d, int i, int j){
    var first= spelling(d.cs().get(i));
    var second= spelling(d.cs().get(j));
    return err()
      .line("Duplicate supertype in type declaration: "+disp(first)+(first.equals(second) ? "." : " and "+disp(second)+" denote the same type."))
      .line("Remove one of them.")
      .wf()
      .addFrame("type declaration "+staticTypeDecName(d.name()), d.span().inner);
  }
  private String spelling(T t){ return switch (t){
    case T.X x -> x.name();
    case T.RCX(var rc, var x) -> rc+" "+x.name();
    case T.ReadImmX(var x) -> "read/imm "+x.name();
    case T.RCC(var rc, var c, _) -> rc.map(r -> r+" ").orElse("")+spelling(c);
  };}
  private String spelling(T.C c){
    var pkg= c.name().pkgName();
    if (map.containsKey(pkg)){ printed.add(map.get(pkg)+"."+c.name().simpleName()); }
    return aliasShown(c.name().s())+Join.of(c.ts().orElse(List.of()).stream().map(this::spelling), "[", ",", "]", "");
  }
  public FearlessException duplicatedName(TName name){
    return err()
      .line("Duplicate type declaration for "+err().tNameADisp(name)+".")
      .wf()
      .addFrame("a type name", name.approxSpan().inner);
  }
  public FearlessException circularImplements(Map<TName,E.Literal> rem){
    var color= new HashMap<TName,Integer>(rem.size());
    var name= rem.keySet().stream().map(k -> _dfs(rem, k, color)).filter(Objects::nonNull).findFirst().get();
    return err()
      .line("Circular implementation relation found involving "+err().tNameADisp(name)+".")
      .wf()
      .addFrame("type declarations", name.approxSpan().inner);
  }
  private TName _dfs(Map<TName,E.Literal> rem, TName u, HashMap<TName,Integer> color){
    var cu= color.get(u);
    if (cu != null){ return cu == 1 ? u : null; }
    color.put(u, 1);
    for (var c : rem.get(u).cs()){
      if (!rem.containsKey(c.name())){ continue; }
      var hit= _dfs(rem, c.name(), color);
      if (hit != null){ return hit; }
    }
    color.put(u, 2);
    return null;
  }
  public FearlessException noSourceToInferFrom(E.Literal origin, M m){
    var size= m.sig().ts().size();
    if (m.sig().m().isEmpty()){
      return wf(err()
        .line("Cannot infer signature and name for a method with "+count(size, "parameter")+".")
        .line("No supertype has a method with "+count(size, "parameter")+"."), m.sig(), origin);
    }
    var name= err().methodSig(m.sig().m().get());
    var allParHasType= m.sig().ts().stream().allMatch(Optional::isPresent);
    var e= err();
    if (allParHasType){
      e.line("Missing return type for method "+name+".")
       .line("Add an explicit return type before '->'.")
       .line("Alternatively (less common), if you intended to override and omit the signature,")
       .line("the signature must be inherited from a supertype.");
    }
    return wf(e
      .line("Cannot infer signature of method "+name+".")
      .line("No supertype has a method named "+name+" with "+count(size, "parameter")+"."), m.sig(), origin);
  }
  public String retTypeDisagreement(){ return "Return type disagreement"; }
  public String paramTypeDisagreement(int i){ return "Type disagreement about parameter "+(i+1); }
  public FearlessException noAgreement(Agreement at, List<B> bs, List<IT> res, String msg){
    var rc= at.rc().map(r -> r.toStrSpace(false)).orElse("");
    var rcDiffers= res.stream().map(t -> t instanceof IT.RCC r ? EnumSet.of(r.rc().orElse(RC.imm)) : Kinding.intrinsicRCs(bs, TypeRename.itToT(t))).distinct().count() > 1;
    var x= res.stream().filter(t -> !(t instanceof IT.RCC)).findFirst();
    var e= err()
      .line(msg+" for method "+methodSig(rc, at.mName())+" with "+count(at.mName().arity(), "parameter")+".")
      .line("Different options are present in the implemented types.")
      .line(Join.of(res.stream().map(o -> option(rcDiffers, o)), "Candidates: ", ", ", "."));
    var m= err().methodSig(at.mName());
    if (rcDiffers){ return wf(e.line("They differ in reference capability, and an overriding method must keep it, so no method "+m+" can implement all of them."), at); }
    if (x.isPresent()){ return wf(e.line("They are different types and "+option(false, x.get())+" is a generic type parameter, so no method "+m+" can implement all of them."), at); }
    return wf(e.line(up(err().expRepr(at.lit()))+" must declare a method "+m+" explicitly choosing the desired option."), at);
  }
  private String option(boolean showImm, IT o){
    if (!(o instanceof IT.RCC rcc)){ return disp(o); }
    return err().typeRepr(!showImm, rcc);
  }
  public FearlessException methodGenericArityDisagreementBetweenSupers(Agreement at, List<List<B>> res){
    var e= err()
      .line("The number of generic type parameters disagrees for method "+err().methodSig(at.mName())
        +" with "+count(at.mName().arity(), "parameter")+".")
      .line("Different options are present in the implemented types.")
      .line(Join.of(res.stream().map(Err::disp), "Candidates: ", ", ", "."))
      .line(up(err().expRepr(at.lit()))+" cannot implement all of those types.");
    return wf(e, at);
  }
  public FearlessException methodGenericArityDisagreesWithSupers(Agreement at, List<B> userBs, List<B> superBs){
    var sB= disp(superBs.stream().map(b -> new B("-", b.rcs())).toList());
    return wf(invalidMethImpl(at)
      .line("The method "+err().methodSig(at.mName())+" declares "+count(userBs.size(), "generic type parameter")+", but supertypes declare "+superBs.size()+".")
      .line("Local declaration: "+disp(userBs)+".")
      .line("From supertypes: "+sB+".")
      .line("Change the local number of generic type parameters to "+superBs.size()+", or adjust the supertypes."), at);
  }
  public FearlessException methodBsDisagreementBetweenSupers(Agreement at, List<List<B>> res){
    assert res.size() >= 2;
    var n= res.getFirst().size();
    assert res.stream().allMatch(bs -> bs.size() == n);
    var i= firstRcsDisagreementIndex(res);
    var opts= Join.of(res.stream().map(bs -> disp(bs.get(i))).distinct().sorted(), "", " and ", ".");
    var m= err().methodSig(at.mName());
    return wf(invalidMethImpl(at)
      .line("Supertypes disagree on the capability bounds for generic type parameter "+(i+1)+" of "+m+".")
      .line("Generic type parameter names may differ across supertypes; only the position matters.")
      .line("Different supertypes declare: "+opts)
      .line(up(err().expRepr(at.lit()))+" cannot implement all of those supertypes.")
      .line("Make the supertypes agree on these bounds, or remove one of the conflicting supertypes."), at);
  }
  public FearlessException methodBsDisagreesWithSupers(Agreement at, List<B> userBs, List<B> superBs){
    assert userBs.size() == superBs.size();
    var i= firstRcsDisagreementIndex(List.of(userBs, superBs));
    var u= userBs.get(i);
    var s= superBs.get(i);
    var m= err().methodSig(at.mName());
    var uB= disp(u);
    var sB= disp(new B("-", s.rcs()));
    return wf(invalidMethImpl(at)
      .line("The local declaration uses different capability bounds than the supertypes for generic type parameter "+(i+1)+" of "+m+".")
      .line("Local: "+uB+".")
      .line("From supertypes: "+sB+".")
      .line("The parameter name may differ; only the position matters.")
      .line("Change the local bounds to match the supertypes, or adjust the supertypes."), at);
  }
  private int firstRcsDisagreementIndex(List<List<B>> res){
    return IntStream.range(0, res.getFirst().size())
      .filter(i -> !res.stream().allMatch(bs -> bs.get(i).rcs().equals(res.getFirst().get(i).rcs())))
      .findFirst().getAsInt();
  }
  public FearlessException captureNotFunnelled(E.X x, IT t, E.Literal owner){
    var xs= B.xs(owner.bs());
    var missing= t.ftv().filter(X -> !xs.contains(X)).findFirst().get();
    var uses= t instanceof IT.RCC ? ", using the generic type parameter "+disp(missing)+"." : ".";
    return wf(err()
      .line("Parameter "+disp(x.name())+" has type "+err().typeRepr(t)+uses)
      .line(Err.funnel(missing, owner.name().simpleName(), xs)), x);
  }
  public FearlessException typeArgAmbiguous(E.Call at, String x, List<IT> cands, List<TName> common, String example, Function<TName,core.E.Literal> decs){
    return typeArgAmbiguous(at, x, disp(at.name().s())+" is inferred from the arguments", cands, common, example, decs);
  }
  public FearlessException literalHeadAmbiguous(E.Literal at, IT.C c, int i, String x, List<IT> cands, List<TName> common, Function<TName,core.E.Literal> decs){
    var example= common.isEmpty() ? "Type"+(i+1) : typeName(common.getFirst());
    var ts= IntStream.range(0, c.ts().size()).mapToObj(j -> j == i ? example : err().typeReprRaw(c.ts().get(j))).toList();
    var lit= err().cp().t.ofFull(c.name())+Join.of(ts, "[", ",", "]")+"{...}";
    return typeArgAmbiguous(at, x, err().tNameADisp(c.name())+" is inferred from the method bodies", cands, common, lit, decs);
  }
  private FearlessException typeArgAmbiguous(E at, String x, String ofFrom, List<IT> cands, List<TName> common, String example, Function<TName,core.E.Literal> decs){
    var cs= cands.stream().map(err(h -> h, n -> n, decs, List.of())::typeRepr).toList();
    var xs= Err.disp(x);
    var e= err().line("The generic type argument "+xs+" of "+ofFrom+", but they disagree: some need "+Join.of(cs, "", ", some need ", "")+".");
    if (common.isEmpty()){ e.line("No type is a supertype of all of them."); }
    else{ e.line(up(xs)+" could be "+Join.of(common.stream().map(n -> disp(err().tNameA(n))), "", " or ", "")+": each is a supertype of "+Join.of(cs, "", " and ", "")+". The choice is ambiguous."); }
    return wf(e.line("Write the generic type argument explicitly, as in "+disp(example)+"."), at);
  }
  public String typeName(TName n){ return err().tNameA(n); }
  public String callWithTargs(E.Call c, List<IT> targs, int k, String example){
    var ts= IntStream.range(0, targs.size()).mapToObj(j -> j == k ? example : err().typeReprRaw(targs.get(j))).toList();
    return src(c.e(), c.name(), Join.of(ts, "[", ",", "]"), c.es());
  }
  private String src(E e){ return switch (e){
    case E.X x -> x.name();
    case E.Literal _ -> "{...}";
    case E.Type t -> err().typeReprRaw(t.type());
    case E.Call c -> src(c.e(), c.name(), "", c.es());
  };}
  private String src(E recv, MName m, String targs, List<E> es){ return src(recv)+m.s()+targs+Join.of(es.stream().map(this::src), "(", ", ", ")", ""); }
  public FearlessException literalHeadNotInferred(E.Literal at, IT.C c, List<Integer> unknown, List<String> xs){
    var head= err().cp().t.ofFull(c.name())+Join.of(c.ts().stream().map(err()::typeReprRaw), "[", ",", "]", "");
    var s= unknown.size() == 1 ? "" : "s";
    return wf(err()
      .line("Type inference concluded that this object literal implements "+disp(head)+",")
      .line("but it could not infer generic type argument"+s+" "+Join.of(unknown.stream().map(i -> i+1), "", " and ", "", "")
        +" for generic type parameter"+s+" "+Join.of(unknown.stream().map(i -> disp(xs.get(i))), "", " and ", "", "")
        +" of "+err().tNameADisp(c.name())+"."), at);
  }
  public FearlessException methodNotInferred(E.Literal at, M.Sig s){
    var n= s.ts().size();
    return wf(err()
      .line("Cannot infer signature and name for a method with "+count(n, "parameter")+".")
      .line("No supertype of "+err().expRepr(at)+" has a method with "+count(n, "parameter")+"."), s, at);
  }
  public FearlessException methodTypeNotInferred(E.Literal at, M.Sig s, MName m, String what){
    return wf(err().line("Cannot infer the type of "+what+" of "+err().methodSig(m)+" in "+err().expRepr(at)+"."), s, at);
  }
  public FearlessException literalImplementsTypeParameter(E.Literal at, IT t){
    return wf(err()
      .line(up(err().expRepr(at))+" cannot implement "+err().typeRepr(t)+".")
      .line(err().typeRepr(t)+" is a generic type parameter; object literals can only implement nominal types."), at);
  }
  public FearlessException typeGrowsForever(E at){
    return wf(err()
      .line("Type inference finds no type for "+err().expRepr(at)+".")
      .line("Each round of inference nests its type one level deeper, as "+err().typeRepr(at.t(), 2)+"; it would grow without bound."), at);
  }
  public FearlessException ambiguousImpl(E.Literal origin, boolean abs, M m, List<M.Sig> options){
    return wf(err()
      .line("Cannot infer the name for a method with "+count(m.sig().ts().size(), "parameter")+".")
      .line("More than one"+(abs ? " abstract" : "")+" method with "+count(m.sig().ts().size(), "parameter")+" could be selected.")
      .line(Join.of(
        options.stream().map(mi -> methodSig(mi.rc().get()+" ", mi.m().get())),
        "Candidates: ", ", ", "."
      )), m.sig(), origin);
  }
  public FearlessException ambiguousImplementationFor(List<TName> options, Agreement at){
    return wf(err()
      .line("Ambiguous implementation for method "+err().methodSig(at.mName())+" with "+count(at.mName().arity(), "parameter")+".")
      .line("Different options are present in the implemented types.")
      .line(Join.of(options.stream().map(err()::tNameADisp), "Candidates: ", ", ", "."))
      .line(up(err().expRepr(at.lit()))+" must declare a method "+err().methodSig(at.mName())+" explicitly implementing the desired behaviour."), at);
  }
  public FearlessException multipleWidenTo(E.Literal owner, List<IT.C> widen){
    var w= err().tNameADisp(LiteralDeclarations.widen);
    var e= err()
      .line(up(err().expRepr(owner))+" implements "+w+" more than once.")
      .line("At most one "+w+" supertype is allowed, because it defines the preferred widened type.")
      .blank()
      .line("Found the following "+w+" supertypes:");
    widen.forEach(c -> e.bullet(claimRepr(owner, c)));
    return wf(e, owner);
  }
  public FearlessException duplicatedNamedLiteral(E.Literal owner, M m, E.Literal in){
    var ctx= up(err().expRepr(owner));
    return wf(err()
      .line(ctx+" implements method "+err().methodSig(m.sig().m().get())+".")
      .line("The body of method "+err().methodSig("", owner, m.sig().m().get())+" needs to be duplicated to satisfy multiple RC overloads from the supertypes.")
      .line("However, it contains "+err().expRepr(in)+".")
      .line("Object literals with their own unique explicit type cannot be duplicated."), owner);
  }
  public FearlessException baseIdNotOnlyHash(E.Literal owner){
    var ctx= up(err().expRepr(owner));
    return wf(err()
      .line(ctx+" implements "+err().tNameADisp(LiteralDeclarations.baseId)+".")
      .line("Only the method "+err().methodSig(new MName("#", 1))+" can be declared or inherited here."), owner);
  }
  public FearlessException baseIdInheritedHash(E.Literal owner, TName origin){
    var ctx= up(err().expRepr(owner));
    return wf(err()
      .line(ctx+" implements "+err().tNameADisp(LiteralDeclarations.baseId)+".")
      .line("It inherits the implementation of "+err().methodSig(new MName("#", 1))+" from "+err().tNameADisp(origin)+", which does not implement "+err().tNameADisp(LiteralDeclarations.baseId)+".")
      .line("Method "+err().methodSig(new MName("#", 1))+" must be implemented here, or inherited from a type implementing "+err().tNameADisp(LiteralDeclarations.baseId)+"."), owner);
  }
  public FearlessException fileLogWithoutFileName(E.Literal owner){
    var ctx= up(err().expRepr(owner));
    var fileLog= err().tNameADisp(LiteralDeclarations.fileLog);
    return wf(err()
      .line(ctx+" implements "+fileLog+", so it writes to a log file named after it.")
      .line("Type name "+disp(owner.name().simpleName())+" has no file name.")
      .line("The name of a "+fileLog+" type can only use letters, digits and underscores, and an underscore cannot be followed by a lowercase letter."), owner);
  }
  public FearlessException fileLogFileNameNotAllowed(E.Literal owner, String path, String why){
    var ctx= up(err().expRepr(owner));
    return wf(err()
      .line(ctx+" implements "+err().tNameADisp(LiteralDeclarations.fileLog)+", so it writes to the log file "+disp(path)+".")
      .line(why)
      .line("Rename "+disp(owner.name().simpleName())+", so that its log file has a name allowed in a Fearless project."), owner);
  }
  public FearlessException namedGeneric(E.Literal owner, TName t, String what){
    return wf(err()
      .line(up(err().expRepr(owner))+" implements "+err().tNameADisp(t)+" and has generic type parameters.")
      .line(what+" implementing "+err().tNameADisp(t)+" must have zero generic type parameters."), owner);
  }
  public FearlessException finalNotMethodName(E.Literal owner, IT.C c){
    return wf(err()
      .line(up(err().expRepr(owner))+" implements "+claimRepr(owner, c)+".")
      .line("The generic type argument of "+err().tNameADisp(LiteralDeclarations.finalMethods)+" is a string literal type holding a method name, like "+disp("\".name\"")+" or "+disp("\"+\"")+"."), owner);
  }
  public FearlessException finalImplemented(E.Literal owner, M m, TName origin, String name){
    var ctx= up(err().expRepr(owner));
    return wf(err()
      .line(ctx+" implements method "+err().methodSig(m.sig().m().get())+".")
      .line(err().tNameADisp(origin)+" implements "+disp(err().cp().t.ofFull(LiteralDeclarations.finalMethods)+"[\""+name+"\"]")+" and "+err().expRepr(owner)+" implements "+err().tNameADisp(origin)+",")
      .line("thus "+err().expRepr(owner)+" cannot override any method named "+disp(name)+"."), owner);
  }
  public FearlessException claimNotMain(E.Literal owner, TName claim){
    var ctx= err().expRepr(owner);
    var c= err().tNameADisp(claim);
    return wf(err()
      .line(up(ctx)+" implements "+c+".")
      .line("Only a main can implement "+c+": "+ctx+" must also implement "+err().tNameADisp(LiteralDeclarations.main)+", directly or through one of its supertypes."), owner);
  }
  public FearlessException claimIconNotConcrete(E.Literal owner, IT.C c){
    return wf(claim(owner, c)
      .line(err().typeRepr(c.ts().getFirst())+" is not a valid icon.")
      .line("Only concrete types with zero generic type arguments are valid icons."), owner);
  }
  public FearlessException claimExtNotStr(E.Literal owner, IT.C c){
    var examples= c.name().simpleName().equals("Shortcut") ? disp("\"fapp042\"") : disp("\"ffile347\"")+", "+disp("\"xml\"")+" or "+disp("\"txt\"");
    return wf(claim(owner, c)
      .line("The extension "+err().typeRepr(c.ts().get(1))+" is not a string literal type.")
      .line("An extension is written as a string literal type, like "+examples+"; "+chooseOne(c)+"."), owner);
  }
  public FearlessException claimExtInvalid(E.Literal owner, IT.C c, String ext){
    return wf(claim(owner, c)
      .line(disp(ext)+" is not a valid extension.")
      .line((ext.equals("fearless") ? "The extension \"fearless\" is reserved" : "An extension is 1 to "+Fs.maxExtSeg+" characters, each a lowercase letter \"a\"-\"z\" or a digit \"0\"-\"9\", with no dot")+"; "+chooseOne(c)+"."), owner);
  }
  public FearlessException claimShortcutNotFapp(E.Literal owner, IT.C c, String ext){
    return wf(claim(owner, c)
      .line(disp(ext)+" is not a shortcut extension: a shortcut file only starts its main, so it must not look like a document of another program or a file of the project.")
      .line("A shortcut extension is \"fapp\" followed by three digits, like \"fapp042\"; "+chooseOne(c)+"."), owner);
  }
  public FearlessException claimOpenWithFapp(E.Literal owner, IT.C c, String ext){
    return wf(claim(owner, c)
      .line(disp(ext)+" is a shortcut extension: \"fapp\" followed by three digits names the shortcut files of the Fearless manager.")
      .line("Use an extension of the form \"ffile\" followed by three digits, like \"ffile042\", or a system extension, like \"htm\"; "+chooseOne(c)+"."), owner);
  }
  public FearlessException claimExtTwice(E.Literal owner, IT.C first, IT.C second, String ext){
    return wf(err()
      .line(up(err().expRepr(owner))+" claims the extension "+disp(ext)+" more than once:")
      .line("both "+claimRepr(owner, first)+" and "+claimRepr(owner, second)+" claim it.")
      .line("A main can claim each extension at most once, across all its "+err().tNameADisp(LiteralDeclarations.claims.get(1))+" and "+err().tNameADisp(LiteralDeclarations.claims.get(3))+", since one extension has one icon."), owner);
  }
  private String chooseOne(IT.C c){ return "or implement "+err().tNameADisp(LiteralDeclarations.claims.get(LiteralDeclarations.claims.indexOf(c.name())-1))+" to let the Fearless manager choose one"; }
  private Err claim(E.Literal owner, IT.C c){ return err().line(up(err().expRepr(owner))+" implements "+claimRepr(owner, c)+"."); }
  private String claimRepr(E.Literal owner, IT.C c){ return disp(err().typeReprRaw(new IT.RCC(Optional.empty(), c, owner.span()))); }
  public FearlessException extendedForeign(E owner, TName target, String kind){
    var targetPkg= target.pkgName();
    assert !pkgName.equals(targetPkg);
    var ctx= up(err().expRepr(owner));
    return wf(err()
      .line(ctx+" implements "+kind+" type "+err().tNameADisp(target)+".")
      .line(up(kind)+" types can only be implemented in their own package.")
      .line(ctx+" is in package "+disp(pkgName)+".")
      .line("Type "+err().tNameADisp(target)+" is in package "+disp(Package.writtenPkg(map, targetPkg))+"."), owner);
  }
  public FearlessException implementsAnonymousType(E.Literal l, E.Literal owner){
    return err()
      .line("The inference concluded that the object literal at "+at(l.span().inner)+" should extend the object literal at "+at(owner.span().inner)+";")
      .line("but an object literal can only extend a standalone type.")
      .line("A type is standalone if it is declared at top level, or if it implements "+err().tNameADisp(LiteralDeclarations.captureFree)+".")
      .wf().addFrame("object literal "+disp("{...}")+" (line "+l.span().inner.startLine()+")", l.span().inner);
  }
  public FearlessException selfNameDeadCode(E.Literal l){
    return wf(err()
      .line("The self name "+disp(l.thisName())+" is dead code.")
      .line("No method of the "+err().expRepr(l)+" uses it.")
      .line("Remove "+disp("'"+l.thisName())+" from the object literal."), l);
  }
  public FearlessException intLiteralOutOfRange(TName lit){
    return intOrNatLiteralOutOfRange(lit, LiteralDeclarations.baseInt, "Integer", "signed", LiteralDeclarations.intMin, LiteralDeclarations.intMax);
  }
  public FearlessException natLiteralOutOfRange(TName lit){
    return intOrNatLiteralOutOfRange(lit, LiteralDeclarations.baseNat, "Natural", "unsigned", LiteralDeclarations.natMin, LiteralDeclarations.natMax);
  }
  private FearlessException intOrNatLiteralOutOfRange(TName lit, TName type, String kind, String signed, BigInteger min, BigInteger max){
    var t= err().tNameADisp(type);
    return err()
      .line(kind+" literal is out of range for "+t+".")
      .line(t+" must be representable as a 64-bit "+signed+" integer.")
      .line("Valid range: "+min+" .. "+max+".")
      .line("This literal is: "+disp(LiteralDeclarations.big(lit.simpleName()))+".")
      .line(numHint())
      .wf().addSpan(lit.approxSpan().inner);
  }
  public FearlessException floatLiteralNotExactlyRepresentable(TName lit){
    var raw= lit.simpleName();
    var d= LiteralDeclarations.floatLiteralDouble(raw);
    var nearD= Double.isFinite(d) ? d : Math.copySign(Double.MAX_VALUE, d);
    var near= LiteralDeclarations.floatExactFearlessLit(nearD);
    var t= err().tNameADisp(LiteralDeclarations.baseFloat);
    var e= err()
      .line("Float literal is not exactly representable as "+t+".")
      .line(t+" must be representable exactly as a 64-bit IEEE 754 double.")
      .line("This literal is: "+disp(raw)+".");
    var at= lit.approxSpan().inner;
    if (!Double.isFinite(d)){ return e.line("This literal overflows; the nearest representable value is "+disp(near)+".").wf().addSpan(at); }
    return e.line("If rounded, the nearest representable value is "+disp(near)+".")
      .line("Write "+disp(raw+LiteralDeclarations.softSuffix)+" to accept that rounding.")
      .line(numHint())
      .wf().addSpan(at);
  }
  private String numHint(){ return "Hint: if you need arbitrary precision numbers, use "+disp(err().cp().t.ofFull(new TName("base.Num", 0, Pos.unknown)))+"."; }
}