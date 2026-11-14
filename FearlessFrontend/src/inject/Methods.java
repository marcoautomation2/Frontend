package inject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.B;
import core.LiteralDeclarations;
import core.MName;
import core.OtherPackages;
import core.RC;
import core.TName;
import fearlessParser.Parser;
import inference.E;
import inference.IT;
import inference.M;
import metaParser.Span;
import naming.FreshPrefix;
import pkgmerge.Package;
import tools.Fs;
import utils.Push;

public record Methods(
    Package p, OtherPackages other, FreshPrefix fresh,
    LinkedHashMap<TName,core.E.Literal> cache){
  boolean free(E.Literal d, Map<TName,E.Literal> rem){ return d.cs().stream().noneMatch(c -> rem.containsKey(c.name())); }
  public static Methods create(Package p, OtherPackages other){
    return new Methods(p, other, new FreshPrefix(p), new LinkedHashMap<>());
  }
  List<E.Literal> supertypesFirst(List<E.Literal> decs){
    var rem= new LinkedHashMap<TName,E.Literal>();
    for (var d : decs){ rem.put(d.name(), d); }
    var out= new ArrayList<E.Literal>();
    while (!rem.isEmpty()){
      var layer= rem.values().stream().filter(d -> free(d, rem)).toList();
      if (layer.isEmpty()){ throw p.err().circularImplements(rem); }
      out.addAll(layer);
      for (var d : layer){ rem.remove(d.name()); }
    }
    return out;
  }
  public List<E.Literal> registerTypeHeadersAndReturnRoots(List<E.Literal> iDecs){
    var acc= new ArrayList<E.Literal>();
    for (var d : supertypesFirst(iDecs)){
      var e= expandDeclaration(d, false);
      if (d.thisName().equals("this")){ acc.add(e); }
      register(e);
    }
    return List.copyOf(acc);
  }
  //TODO: performance: currently fetch rewrites for the class generics
  //but we are likely to also do the rewriting for the meth generics very soon later.
  //can we merge the two steps? Something similar has been done for MSigL
  List<M.Sig> fetchSigs(E.Literal child, IT.C c, core.E.Literal d, List<String> scope){ //d == from(c.name()); but from can be undefined for {..}.foo
    return d.ms().stream().map(m -> alphaSig(m, d, c, child, scope)).toList();
  }
  List<IT.C> implied(IT.C c){
    var d= _from(c.name());
    if (d == null){ return List.of(); }//case {..}.foo
    return d.cs().stream().map(TypeRename::tcToITC).map(ci -> TypeRename.of(ci, B.xs(d.bs()), c.ts())).distinct().toList();
  }
  private List<TName> superHeads(TName n){
    var d= _from(n);
    return d == null ? List.of() : d.cs().stream().map(core.T.C::name).toList();
  }
  List<TName> commonSuperHeads(List<IT> cands){
    if (!cands.stream().allMatch(t -> t instanceof IT.RCC)){ return List.of(); }
    var heads= cands.stream().map(t -> new ArrayList<>(superHeads(((IT.RCC)t).c().name()))).reduce((a,b) -> { a.retainAll(b); return a; }).get();
    heads.removeIf(h -> cands.stream().flatMap(t -> implied(((IT.RCC)t).c()).stream().filter(c -> c.name().equals(h))).distinct().count() != 1);
    return heads.stream().filter(h -> heads.stream().noneMatch(h2 -> !h2.equals(h) && superHeads(h2).contains(h))).toList();
  }
  private M.Sig alphaSig(core.M m, core.E.Literal d, IT.C c, E.Literal child, List<String> scope){
    var s= m.sig();
    var fullXs= new ArrayList<>(B.xs(d.bs()));
    var fullTs= new ArrayList<>(c.ts());
    var newBs= new ArrayList<B>(s.bs().size());
    for (var b : s.bs()){
      var x= b.x();
      if (fresh.isFreshGeneric(child.name(), x, scope)){ newBs.add(b); continue; }
      assert !fullXs.contains(x);
      fullXs.add(x);
      var newX= new IT.X(fresh.freshGeneric(child.name(), x, Push.of(B.xs(s.bs()), scope)), child.name().approxSpan());
      fullTs.add(newX);
      newBs.add(new B(newX.name(), b.rcs()));
    }
    var newTs= TypeRename.ofIT(TypeRename.tToIT(s.ts()), fullXs, fullTs).stream().map(Optional::of).toList();
    var newRet= TypeRename.of(TypeRename.tToIT(s.ret()), fullXs, fullTs);
    return new M.Sig(s.rc(), s.m(), Collections.unmodifiableList(newBs), newTs, newRet, s.origin(), s.abs(), child.span());
  }
  public core.E.Literal from(TName name){ return Objects.requireNonNull(_from(name)); }
  core.E.Literal _from(TName name){ return LiteralDeclarations._from(name, cache::get, other); }
  public E.Literal expandDeclaration(E.Literal d, boolean setInfHead){
    var implied= d.cs().stream().flatMap(c -> implied(c).stream()).toList();
    var allCs= ToCore.distinctTypes(d.bs(), Push.of(d.cs(), implied.stream().sorted(Comparator.comparing(Object::toString)).toList()));
    var allSig= d.cs().stream().filter(c -> !implied.contains(c)).flatMap(c -> fetchSigs(d, c, from(c.name()), List.of()).stream()).toList();
    var allMs= pairWithSig(inferMNames(d.ms(), new ArrayList<>(allSig), d), new ArrayList<>(allSig), d);
    var res= d.withCsMs(allCs, allMs, setInfHead);
    checkMagicSupertypes(res, allCs);
    return res;
  }
  //expandLiteral works on an incomplete literal with the cs list not there yet
  public E.Literal expandLiteral(E.Literal d, IT.C c, List<B> scope){//Correct to have both expandLiteral and expandDeclaration
    var dd= _from(c.name());//null for the case {..}.foo
    List<M.Sig> allSig= dd == null ? List.of() : fetchSigs(d, c, dd, B.xs(scope));
    var allMs= pairWithSig(inferMNames(d.ms(), new ArrayList<>(allSig), d), new ArrayList<>(allSig), d);
    return d.withCsMs(Push.of(c, implied(c)), allMs, true);
  }
  public void checkMagicSupertypes(E.Literal d, List<IT.C> allCs){
    var names= allCs.stream().map(IT.C::name).toList();
    var widen= allCs.stream().filter(c -> c.name().equals(LiteralDeclarations.widen)).toList();
    if (widen.size() > 1){ throw p.err().multipleWidenTo(d, widen); }
    if (names.contains(LiteralDeclarations.baseId)){ checkBaseId(d); }
    if (names.contains(LiteralDeclarations.fileLog)){ checkFileLogName(d); }
    checkClaims(d, names, allCs);
    allCs.stream().filter(c -> c.name().equals(LiteralDeclarations.finalMethods)).forEach(c -> checkFinal(d, finalMethod(d, c), allCs));
    for (var n : LiteralDeclarations.notGeneric){
      if (names.contains(n) && !d.bs().isEmpty()){ throw p.err().namedGeneric(d, n, "A type"); }
    }
    var concrete= d.ms().stream().allMatch(m -> m.impl().isPresent() || !m.sig().abs());
    for (var n : LiteralDeclarations.concreteNotGeneric){
      if (names.contains(n) && concrete && !d.bs().isEmpty()){ throw p.err().namedGeneric(d, n, "A concrete type"); }
    }
    if (!names.contains(LiteralDeclarations.sealed)){ return; }
    allCs.stream()
      .filter(c -> !c.name().pkgName().equals(d.name().pkgName()))
      .forEach(c -> notSealed(c.name(), d));
  }
  private void checkBaseId(E.Literal d){
    var ms= d.ms();
    var onlyHash= ms.size() == 1;
    if (!onlyHash){ throw p.err().baseIdNotOnlyHash(d); }
    var s= ms.getFirst().sig();
    var origin= s.origin().get();
    var validHash= ms.getFirst().impl().isPresent() || s.abs() || LiteralDeclarations.has(from(origin).cs(), LiteralDeclarations.baseId);
    if (validHash){ return; }
    throw p.err().baseIdInheritedHash(d, origin);
  }
  private void checkFileLogName(E.Literal d){
    var file= Fs.fileNameOfType(d.name().simpleName()).orElseThrow(() -> p.err().fileLogWithoutFileName(d));
    var path= ".out/logs/_"+d.name().pkgName()+"/"+file+".log";
    if (Fs.winReserved.contains(file)){ throw p.err().fileLogFileNameNotAllowed(d, path, "\""+file+"\" is a Windows reserved device name."); }
    if (file.startsWith("_rank_")){ throw p.err().fileLogFileNameNotAllowed(d, path, "Only rank files can start with \"_rank_\"."); }
    if (path.length() > 200){ throw p.err().fileLogFileNameNotAllowed(d, path, "The path is longer than 200 characters."); }
  }
  private void checkClaims(E.Literal d, List<TName> names, List<IT.C> allCs){
    var cs= allCs.stream().filter(c -> LiteralDeclarations.claims.contains(c.name())).toList();
    if (cs.isEmpty()){ return; }
    if (!names.contains(LiteralDeclarations.main)){ throw p.err().claimNotMain(d, cs.getFirst().name()); }
    var exts= new HashMap<String,IT.C>();
    for (var c : cs){
      if (!(c.ts().getFirst() instanceof IT.RCC i && i.c().ts().isEmpty())){ throw p.err().claimIconNotConcrete(d, c); }
      if (c.ts().size() == 1){ continue; }
      var lit= c.ts().get(1) instanceof IT.RCC e ? e.c().name().simpleName() : "";
      if (!lit.startsWith("\"") && !lit.startsWith("`")){ throw p.err().claimExtNotStr(d, c); }
      var ext= lit.substring(1, lit.length()-1);
      if (!Fs.isExtSeg(ext) || ext.equals("fearless")){ throw p.err().claimExtInvalid(d, c, ext); }
      var shortcut= c.name().simpleName().equals("Shortcut");
      if (shortcut != ext.matches("fapp[0-9]{3}")){ throw shortcut ? p.err().claimShortcutNotFapp(d, c, ext) : p.err().claimOpenWithFapp(d, c, ext); }
      var prev= exts.putIfAbsent(ext, c);
      if (prev != null){ throw p.err().claimExtTwice(d, prev, c, ext); }
    }
  }
  private String finalMethod(E.Literal d, IT.C c){
    var lit= c.ts().getFirst() instanceof IT.RCC e ? e.c().name().simpleName() : "";
    var quoted= lit.startsWith("\"") || lit.startsWith("`");
    var m= quoted ? lit.substring(1, lit.length()-1) : "";
    if (!MName.isMethodName(m)){ throw p.err().finalNotMethodName(d, c); }
    return m;
  }
  private void checkFinal(E.Literal d, String m, List<IT.C> allCs){
    var heirs= allCs.stream().filter(o -> !o.name().equals(LiteralDeclarations.finalMethods) && implied(o).stream().anyMatch(c -> c.name().equals(LiteralDeclarations.finalMethods) && finalMethod(d, c).equals(m))).toList();
    if (heirs.isEmpty()){ return; }
    var origin= heirs.stream().filter(o -> heirs.stream().noneMatch(h -> implied(o).stream().anyMatch(c -> c.name().equals(h.name())))).findFirst().orElseThrow();
    d.ms().stream().filter(mi -> mi.sig().m().get().s().equals(m) && mi.sig().origin().equals(Optional.of(d.name()))).findFirst()
      .ifPresent(mi -> { throw p.err().finalImplemented(d, mi, origin.name(), m); });
  }
  void notSealed(TName target, E.Literal owner){
    var targetSealed= LiteralDeclarations.has(from(target).cs(), LiteralDeclarations.sealed);
    if (!targetSealed){ return; }
    throw p.err().extendedForeign(owner, target, "sealed");
  }

  void register(E.Literal d){
    var cs= TypeRename.itcToTC(d.cs());
    assert InjectionToInferenceVisitor.duplicatedSupertypes(d.bs(), d.cs()).isEmpty();
    assert !d.infName() || !d.thisName().equals("_") || d.ms().stream().anyMatch(m -> m.impl().isPresent());
    p.log().logInferenceDeclaration(d, cs);
    var ms= d.ms().stream().map(new ToCore(List.of(), this)::mSynthetic).toList();
    cache.put(d.name(), new core.E.Literal(d.rc().orElse(RC.imm), d.name(), d.bs(), cs, d.thisName(), ms, d.src(), d.infName()));
  }
  List<M> inferMNames(List<M> ms, ArrayList<M.Sig> ss, E.Literal origin){
    assert ss.stream().allMatch(M.Sig::isFull);
    var res= new ArrayList<M>(ms.size());
    var changed= false;
    for (var m : ms){//for methods WITH name
      if (m.sig().m().isEmpty()){ continue; }
      var name= m.sig().m().get();
      ss.removeIf(s -> s.m().get().equals(name));
      res.add(m);
    }
    for (var m : ms){//for methods WITHOUT name
      if (m.sig().m().isPresent()){ continue; }
      changed = true;
      res.add(nameFromSigs(m, ss, origin));
    }
    return changed ? List.copyOf(res) : ms;
  }
  M withName(MName name, M m){
    assert m.impl().isPresent();
    assert m.sig().m().isEmpty();
    var s= m.sig();
    return new M(new M.Sig(s.rc(), Optional.of(name), s.bs(), s.ts(), s.ret(), s.origin(), s.abs(), s.span()), m.xs(), m.names(), m.impl());
  }
  private M nameFromSigs(M m, ArrayList<M.Sig> ss, E.Literal origin){
    var arity= m.sig().ts().size();
    for (var abs : List.of(true, false)){
      var match= ss.stream().filter(s -> s.m().get().arity() == arity && (s.abs() || !abs)).toList();
      ss.removeAll(match);
      var count= match.stream().map(s -> s.m().get()).distinct().count();
      if (count == 1){ return withName(match.getFirst().m().get(), m); }
      if (count > 1){ throw p.err().ambiguousImpl(origin, abs, m, match); }
    }
    throw p.err().noSourceToInferFrom(origin, m);
  }
  List<M> pairWithSig(List<M> ms, ArrayList<M.Sig> ss, E.Literal origin){
    var res= new ArrayList<M>();
    var changed= false;
    for (var m : ms){
      var name= m.sig().m().get();
      var rc= m.sig().rc();
      var taken= ss.stream().filter(s -> s.m().get().equals(name) && (rc.isEmpty() || rc.equals(s.rc()))).toList();
      ss.removeAll(taken);
      var match= taken.stream().collect(Collectors.groupingBy(s -> s.rc().get(), LinkedHashMap::new, Collectors.toList()));
      var inferredRcOverloads= rc.isEmpty() && match.size() > 1;
      if (inferredRcOverloads){
        var litRc= origin.rc().or(origin.t()::explicitRC).orElse(RC.imm);
        var neverMut= InjectionSteps.noH(litRc).isReadOrImm();
        if (neverMut){
          var dead= match.remove(RC.mut);
          if (dead != null){ ss.addAll(dead); }
        }
      }
      List<List<M.Sig>> groups= match.isEmpty() ? List.of(List.of()) : List.copyOf(match.values());
      var first= true;
      for (var matches : groups){
        var mi= first ? m : new DupE(fresh, origin, m, p.err()).ofM(m, origin.name(), origin.name());
        first = false;
        var m2= pairWithSig(Collections.unmodifiableList(matches), mi, origin);
        assert (m2 == mi) == m2.equals(mi);
        changed |= m2 != mi;
        res.add(m2);
      }
      //--------
    }
    if (!ss.isEmpty()){
      changed = true;
      ss.stream()
        .collect(Collectors.groupingBy(
          s -> new Parser.RCMName(s.rc(), s.m().get()),
          LinkedHashMap::new,
          Collectors.toList()))
        .values()
        .forEach(v -> res.add(pairWithSig(v, origin)));
    }
    assert !changed == res.equals(ms);
    return changed ? List.copyOf(res) : ms;
  }

  M pairWithSig(List<M.Sig> ss, M m, E.Literal origin){
    if (ss.isEmpty()){ return toCompleteM(m, origin); }
    var s= m.sig();
    var at= new Agreement(origin, ss.getFirst().rc(), ss.getFirst().m().get(), m.sig().span().inner);
    var bs= agreementWithSize(ss, s, at);
    var ssAligned= alignMethodSigsTo(ss, bs);
    var name= ssAligned.getFirst().m().get();
    var ts= IntStream.range(0, s.ts().size()).mapToObj(i -> Optional.of(pairWithTs(at, i, s.ts().get(i), ssAligned))).toList();
    var res= s.ret().orElseGet(() -> agreement(at, ssAligned, e -> e.ret().get(),
      p.err().retTypeDisagreement()));
    var rc= s.rc().orElseGet(() -> rcAgreement(ssAligned));
    return m.withSig(new M.Sig(rc, name, bs, ts, res, origin.name(), m.impl().isEmpty(), s.span()));
  }
  private List<B> agreementWithSize(List<M.Sig> ss, M.Sig s, Agreement at){
    var allBounds= ss.stream().map(e -> e.bs().get()).distinct().toList();
    if (s.bs().isEmpty()){ return agreementBs(at, allBounds); }
    var userBs= s.bs().get();
    var superBsList= ss.stream().map(e -> e.bs().get()).toList();
    var superArities= superBsList.stream().map(List::size).distinct().toList();
    if (superArities.size() != 1){ throw p.err().methodGenericArityDisagreementBetweenSupers(at, superBsList); }
    if (superArities.getFirst() != userBs.size()){ throw p.err().methodGenericArityDisagreesWithSupers(at, userBs, superBsList.getFirst()); }
    var supBs= agreementBs(at, allBounds);
    assert supBs.size() == userBs.size();
    var supRCs= supBs.stream().map(B::rcs).toList();
    var userRCs= userBs.stream().map(B::rcs).toList();
    if (supRCs.equals(userRCs)){ return userBs; }
    throw p.err().methodBsDisagreesWithSupers(at, userBs, supBs);
  }
  IT pairWithTs(Agreement at, int i, Optional<IT> t, List<M.Sig> ss){
    return t.orElseGet(() -> agreement(at, ss, e -> e.ts().get(i).get(),
      p.err().paramTypeDisagreement(i)));
  }
  M pairWithSig(List<M.Sig> ss, E.Literal origin){
    assert !ss.isEmpty();
    if (ss.size() == 1){ return unnamed(ss.getFirst()); }
    var at= new Agreement(origin, ss.getFirst().rc(), ss.getFirst().m().get(), origin.span().inner);
    var bs= agreementBs(at, ss.stream().map(e -> e.bs().get()).distinct().toList());
    var ssAligned= alignMethodSigsTo(ss, bs);
    var name= ssAligned.getFirst().m().get();
    var ts= IntStream.range(0, name.arity()).mapToObj(i -> Optional.of(pairWithTs(at, i, Optional.empty(), ssAligned))).toList();
    var res= agreement(at, ssAligned, e -> e.ret().get(), p.err().retTypeDisagreement());
    var impl= ssAligned.stream().filter(e -> !e.abs() && !overridden(e, origin)).map(e -> e.origin().get()).distinct().toList();
    if (impl.size() > 1){ throw p.err().ambiguousImplementationFor(impl, at); }
    var originName= impl.size() == 1 ? impl.getFirst() : origin.name();
    var rc= rcAgreement(ssAligned);
    var sig= new M.Sig(rc, name, bs, ts, res, originName, impl.isEmpty(), ssAligned.getFirst().span());
    return unnamed(sig);
  }
  static M unnamed(M.Sig s){
    var xs= Collections.nCopies(s.ts().size(), "_");
    return new M(s, xs, xs, Optional.empty());
  }

  private boolean overridden(M.Sig s, E.Literal lit){
    var sup= s.origin().get();
    return lit.cs().stream()
      .flatMap(c -> Stream.concat(Stream.of(c.name()), from(c.name()).cs().stream().map(core.T.C::name)))
      .anyMatch(t -> !t.equals(sup) && declares(from(t), sup, s));
  }
  private boolean declares(core.E.Literal d, TName sup, M.Sig s){
    return LiteralDeclarations.has(d.cs(), sup) && d.ms().stream().map(core.M::sig)
      .anyMatch(o -> o.origin().equals(d.name()) && o.m().equals(s.m().get()) && o.rc() == s.rc().get());
  }
  M toCompleteM(M m, E.Literal origin){
    var s= m.sig();
    var ts= s.ts().stream().map(t -> Optional.of(t.orElseThrow(() -> p.err().noSourceToInferFrom(origin, m)))).toList();
    var res= s.ret().orElseThrow(() -> p.err().noSourceToInferFrom(origin, m));
    return m.withSig(new M.Sig(s.rc().orElse(RC.imm), s.m().get(), s.bs().orElse(List.of()), ts, res, origin.name(), m.impl().isEmpty(), s.span()));
  }
  private IT agreement(Agreement at, List<M.Sig> ss, Function<M.Sig,IT> f, String msg){
    var res= ss.stream().map(f).distinct().toList();
    var bs= Push.of(at.lit().bs(), ss.getFirst().bs().get());
    var first= res.getFirst();
    var same= res.stream().allMatch(t -> TypeRename.eqModXRC(bs, first, t));
    if (same){ return res.getFirst(); }
    throw p.err().noAgreement(at, bs, res, msg);
  }
  //ssAligned is always grouped/bucketed by rc upstream (see pairWithSig callers), so rc is always uniform here.
  private RC rcAgreement(List<M.Sig> ssAligned){
    var rc= ssAligned.getFirst().rc().get();
    assert ssAligned.stream().allMatch(e -> e.rc().get() == rc);
    return rc;
  }
  public record Agreement(E.Literal lit, Optional<RC> rc, MName mName, Span span){}

  List<B> agreementBs(Agreement at, List<List<B>> res){
    var sizes= res.stream().map(List::size).distinct().count();
    if (sizes != 1){ throw p.err().methodGenericArityDisagreementBetweenSupers(at, res); }
    var bounds= res.stream().map(l -> l.stream().map(B::rcs).toList()).distinct().count();
    if (bounds == 1){ return res.getFirst(); }
    throw p.err().methodBsDisagreementBetweenSupers(at, res);
  }
  private List<M.Sig> alignMethodSigsTo(List<M.Sig> ss, List<B> bs){ return ss.stream().map(s -> alignMethodSigTo(s, bs)).toList(); }
  private M.Sig alignMethodSigTo(M.Sig superSig, List<B> targetBs){
    assert superSig.isFull();
    var fromXs= B.xs(superSig.bs().get());
    var toITs= MSigL.toXs(superSig.span(), B.xs(targetBs));
    assert fromXs.size() == toITs.size();
    var renamedTs= superSig.ts().stream().map(t -> Optional.of(TypeRename.of(t.get(), fromXs, toITs))).toList();
    var renamedRet= superSig.ret().map(it -> TypeRename.of(it, fromXs, toITs));
    return new M.Sig(superSig.rc(), superSig.m(), Optional.of(targetBs),
      renamedTs, renamedRet, superSig.origin(), superSig.abs(), superSig.span());
  }
}