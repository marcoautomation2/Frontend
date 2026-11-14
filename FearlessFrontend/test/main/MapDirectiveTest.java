package main;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import core.AllLs;
import core.FearlessException;
import core.OtherPackages;
import testUtils.DbgBlock;

public final class MapDirectiveTest extends testUtils.FearlessTestBase{
  static final String aA= "A:{.fromA:A->this}";
  static final String cA= "A:{.fromC:A->this}";
  static final String dA= "A:{.fromD:A->this}";
  static OtherPackages others(Map<String,String> pkgs){
    var res= otherFrom(DbgBlock.all());
    for (var e : pkgs.entrySet()){
      var o= oraclePkg(List.of(e.getValue()));
      var lits= compileAll(e.getKey(), o, otherFrom(DbgBlock.all()));
      res = res.mergeWith(AllLs.of(lits), -1);
    }
    return res;
  }
  static void ok(Map<String,String> pkgs, Map<String,String> map, String bSrc){
    var o= oraclePkg(List.of(bSrc));
    var other= others(pkgs);
    var res= okOrPrint(o, () -> new FrontendLogicMain().of("b", writtenIn(map), o.allFiles(), other));
    if (!checkCompact){ return; }
    coreCmp(lines(res), compact.Print.lines(compactB(pkgs, map, o)));
  }
  static void fail(String expected, Map<String,String> pkgs, Map<String,String> map, String bSrc){
    var o= oraclePkg(List.of(bSrc));
    var other= others(pkgs);
    var fe= assertThrows(FearlessException.class, () -> new FrontendLogicMain().of("b", writtenIn(map), o.allFiles(), other));
    strCmp(expected, fe.render(o));
    if (!checkCompact){ return; }
    assertThrows(compact.Frontend.Fail.class, () -> compactB(pkgs, map, o));
  }
  static Map<String,String> writtenIn(Map<String,String> map){
    return map.entrySet().stream().collect(java.util.stream.Collectors.toMap(Map.Entry::getKey, e -> e.getValue()+" fear:/_b/_rank_app.fear"));
  }
  static List<compact.Frontend.Literal> compactB(Map<String,String> pkgs, Map<String,String> map, tools.SourceOracle o){
    var base= compactBase();
    var other= new ArrayList<>(base);
    for (var e : pkgs.entrySet()){ compactAll(e.getKey(), oraclePkg(List.of(e.getValue())), base).stream().flatMap(MapDirectiveTest::compactAllLs).forEach(other::add); }
    return compactAll("b", map, o, other);
  }
  @Test void typingContextShowsSupertypeWrittenThroughAMap(){ fail("""
In file: [###].fear

001| B:a.A{ .fromC -> base.Void }
   |        ----------^^^^^^^^^

While inspecting object literal instance of "base.Void" > ".fromC" line 1
The body of method ".fromC" of type declaration "B" is an expression returning "iso base.Void".
Object literal is of type "base.Void" instead of a subtype of "a.A".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "a.A" was introduced: (compression indicated by `-`)
B:-.A{.fromC:-.A->-.Void}
Error 8 TypeError""", Map.of("c", cA), Map.of("a", "c"), """
B:a.A{ .fromC -> base.Void }
"""); }
  @Test void typeErrorWritesTheMappedName(){ fail("""
In file: [###].fear

001| B:{.k(x:a.A):B->x.m}
   |    -------------^^^^

While inspecting method call ".m" > ".k(_)" line 1
The body of method ".k(_)" of type declaration "B" is an expression returning "a.A".
Method call "a.A.m" has type "a.A" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.k(x:-.A):B->x.m}
Error 8 TypeError""", Map.of("c", "A:{.m:A->this}"), Map.of("a", "c"), """
B:{.k(x:a.A):B->x.m}
"""); }
  @Test void inferenceErrorWritesTheMappedName(){ fail("""
In file: [###].fear

001| B:a.A,a.A2{}
   | ^^^^^^^^^^^^

While inspecting type declaration "B"
Return type disagreement for method "imm .m" with 0 parameters.
Different options are present in the implemented types.
Candidates: "a.A", "a.A2".
Type declaration "B" must declare a method ".m" explicitly choosing the desired option.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness""", Map.of("c", "A:{.m:A->this} A2:{.m:A2->this}"), Map.of("a", "c"), """
B:a.A,a.A2{}
"""); }
  @Test void mapToMissingTypeSuggestsNoNameTheMapRedirects(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):B->this}
   |         ^^^^

While inspecting a type name
Type "A" is not declared in package "a".
In scope: "a.C".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "C:{}"), Map.of("a", "c"), """
B:{.m(x:a.A):B->this}
"""); }
  @Test void noMapQualifiedNameIsLiteral(){ ok(Map.of("a", aA, "c", cA), Map.of(), """
B:{.m(x:a.A):a.A->x.fromA}
"""); }
  @Test void mappedNameStandsForTheOutPackage(){ ok(Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:a.A):a.A->x.fromC}
"""); }
  @Test void outPackageIsNotReachableByItsOwnName(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):c.A->x.fromC}
   |              ^^^^

While inspecting a type name
Source code inside folders named "_b" cannot use package name "c".
Did you mean "a" ?
Visible package names: "a", "base".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:a.A):c.A->x.fromC}
"""); }
  @Test void useOfTheCurrentPackage(){ fail("""
In file: [###].fear

001| use b.B as X;
   |     ^^^

While inspecting package header
"use" directive refers to type "B" declared inside folders named "_b".
A "use" directive can only refer to types declared in other folders.
Source code inside folders named "_b" uses the simple names of its own types.
Error 7 WellFormedness""", Map.of(), Map.of(), """
use b.B as X;
B:{.m(x:X):B->x.self; .self:X->this}
"""); }
  @Test void currentPackageQualified(){ fail("""
In file: [###].fear

001| B:{.m(x:b.B):B->this}
   |         ^^^^

While inspecting a type name
The full type name "b.B" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "B" to refer to "b.B".
Error 7 WellFormedness
""", Map.of(), Map.of(), """
B:{.m(x:b.B):B->this}
"""); }
  @Test void currentPackageQualifiedUndeclared(){ fail("""
In file: [###].fear

001| B:{.m(x:b.Z):B->this}
   |         ^^^^

While inspecting a type name
Type "Z" is not declared in package "b".
In scope: "B".
Error 7 WellFormedness
""", Map.of(), Map.of(), """
B:{.m(x:b.Z):B->this}
"""); }
  @Test void currentPackageQualifiedOtherArity(){ fail("""
In file: [###].fear

001| B:{.m(x:b.B[B]):B->this}
   |         ^^^^

While inspecting a type name
Name "B" is not declared with 1 generic type parameter in package "b".
Name "B" is only declared with 0 generic type parameters.
Did you accidentally add or omit a generic type argument?
Error 7 WellFormedness
""", Map.of(), Map.of(), """
B:{.m(x:b.B[B]):B->this}
"""); }
  @Test void mapTargetQualifiedUndeclared(){ fail("""
In file: [###].fear

001| B:{.m(x:c.Z):B->this}
   |         ^^^^

While inspecting a type name
Source code inside folders named "_b" cannot use package name "c".
Did you mean "a" ?
Visible package names: "a", "base".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:c.Z):B->this}
"""); }
  @Test void currentPackageQualifiedWithOtherOptions(){ fail("""
In file: [###].fear

002| B:{.m(x:b.B):B->this}
   |         ^^^^

While inspecting a type name
The full type name "b.B" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "B" to refer to "b.B".
Did you mean "a.B" or "d.B" ?

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "B:{}", "d", "B:{}", "e", "B:{}"), Map.of("a", "c"), """
use e.B as EB;
B:{.m(x:b.B):B->this}
"""); }
  @Test void useOfAMissingPackage(){ fail("""
In file: [###].fear

001| use zz.A as X;
   |     ^^^^

While inspecting package header
Source code inside folders named "_b" cannot use package name "zz".
Visible package names: "base".
Error 7 WellFormedness
""", Map.of(), Map.of(), """
use zz.A as X;
B:{}
"""); }
  @Test void mapToMissingType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Z):B->this}
   |         ^^^^

While inspecting a type name
Type "Z" is not declared in package "a".
In scope: "a.A".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:a.Z):B->this}
"""); }
  @Test void useThroughMap(){ ok(Map.of("c", cA), Map.of("a", "c"), """
use a.A as A;
B:{.m(x:A):A->x.fromC}
"""); }
  @Test void useThroughMapToMissingType(){ fail("""
In file: [###].fear

001| use a.Z as Z;
   |     ^^^

While inspecting package header
"use" directive refers to type "Z", which is not declared in package "a".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_cc", because of "map a as _cc in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("cc", cA), Map.of("a", "cc"), """
use a.Z as Z;
B:{}
"""); }
  @Test void useOfAMapTarget(){ fail("""
In file: [###].fear

001| use c.A as X;
   |     ^^^

While inspecting package header
Source code inside folders named "_b" cannot use package name "c".
Did you mean "a" ?
Visible package names: "a", "base".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use c.A as X;
B:{.m(x:X):X->x.fromC}
"""); }
  @Test void aliasedTypeWrittenQualified(){ fail("""
In file: [###].fear

002| B:{.m(x:X):c.A->x.fromC}
   |            ^^^^

While inspecting a type name
The full type name "c.A" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "X" to refer to "c.A", because of "use c.A as X".
Error 7 WellFormedness
""", Map.of("c", cA), Map.of(), """
use c.A as X;
B:{.m(x:X):c.A->x.fromC}
"""); }
  @Test void aliasedTypeWrittenThroughAMap(){ fail("""
In file: [###].fear

002| B:{.m(x:X):a.A->x.fromC}
   |            ^^^^

While inspecting a type name
The full type name "a.A" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "X" to refer to "a.A", because of "use a.A as X".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:X):a.A->x.fromC}
"""); }
  @Test void useThroughMapFail(){ fail("""
In file: [###].fear

002| B:{.m(x:A):A->x.fromA}
   |    -----------~^^^^^^^

While inspecting ".m(_)" line 2
This call to method ".fromA" cannot typecheck.
Method ".fromA" is not declared on type "A".

Available methods on type "A":
-       .fromC:A

Name "A" stands for "a.A" because of "use a.A as A".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.fromA
Error 8 TypeError
""", Map.of("c", cA), Map.of("a", "c"), """
use a.A as A;
B:{.m(x:A):A->x.fromA}
"""); }
  @Test void useWithoutMapFailHasNoNote(){ fail("""
In file: [###].fear

002| B:{.m(x:X):X->x.fromA}
   |    -----------~^^^^^^^

While inspecting ".m(_)" line 2
This call to method ".fromA" cannot typecheck.
Method ".fromA" is not declared on type "X".

Available methods on type "X":
-       .fromC:X

Compressed relevant code with inferred types: (compression indicated by `-`)
x.fromA
Error 8 TypeError
""", Map.of("c", cA), Map.of(), """
use c.A as X;
B:{.m(x:X):X->x.fromA}
"""); }
  @Test void useOfOtherPackageOtherArity(){ fail("""
In file: [###].fear

002| B:{.m(x:X[B]):B->this}
   |         ^^

While inspecting a type name
Name "A" is not declared with 1 generic type parameter in package "c".
Name "A" is only declared with 0 generic type parameters.
Did you accidentally add or omit a generic type argument?

Name "X" stands for "c.A" because of "use c.A as X".
Error 7 WellFormedness
""", Map.of("c", cA), Map.of(), """
use c.A as X;
B:{.m(x:X[B]):B->this}
"""); }
  @Test void useThroughMapOtherArity(){ fail("""
In file: [###].fear

002| B:{.m(x:X[B]):B->this}
   |         ^^

While inspecting a type name
Name "A" is not declared with 1 generic type parameter in package "a".
Name "A" is only declared with 0 generic type parameters.
Did you accidentally add or omit a generic type argument?

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:X[B]):B->this}
"""); }
  @Test void twoVersionsOfAPackageMappedFromTwoNames(){ ok(Map.of("webserver_v12", "Server:{.v12:Server->this}", "webserver_v13", "Server:{.v13:Server->this}"), Map.of("old", "webserver_v12", "webserver", "webserver_v13"), """
B:{.m(x:old.Server, y:webserver.Server):webserver.Server->y.v13; .k(x:old.Server):old.Server->x.v12}
"""); }
  @Test void versionFolderNameWrittenAsAPackageName(){ fail("""
In file: [###].fear

001| B:{.m(x:webserver_v12.Server):webserver.Server->x.v12}
   |         ^^^^^^^^^^^^^^^^^^^^^

While inspecting a type name
Source code inside folders named "_b" cannot use package name "webserver_v12".
Did you mean "webserver" ?
Visible package names: "base", "webserver".
Source code inside folders named "_b" uses package name "webserver" to refer to the code inside folders named "_webserver_v12", because of "map webserver as _webserver_v12 in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("webserver_v12", "Server:{.v12:Server->this}"), Map.of("webserver", "webserver_v12"), """
B:{.m(x:webserver_v12.Server):webserver.Server->x.v12}
"""); }
  static final String pq= "P:{ .x:P->this; .y:P->this; }\n";
  @Test void destructuringWithAnAliasForDestruct(){ ok(Map.of(), Map.of(), """
use base.Destruct as D;
"""+pq+"""
B:{ .m({.x, .y}:P):P -> x }
"""); }
  @Test void destructuringInsideBase(){
    var b= tools.SourceOracle.debugBuilder();
    DbgBlock.dbgMiniBase().allFiles().forEach(r -> b.putURI(r.fearURI(), r.loadString()));
    var o= b.put("baseExtra.fear", "Pq:{ .x:Pq->this; .y:Pq->this; }\nUsesDestruct:{ .m({.x, .y}:Pq):Pq -> y }\n").build();
    var res= okOrPrint(o, () -> new FrontendLogicMain().of("base", Map.of(), o.allFiles(), OtherPackages.empty()));
    if (!checkCompact){ return; }
    coreCmp(lines(res), compact.Print.lines(compactAll("base", o, List.of())));
  }
  @Test void destructuringWithBaseReachedThroughAMap(){ ok(Map.of(), Map.of("bb", "base"), pq+"""
B:{ .m({.x, .y}:P):P -> y }
"""); }
  @Test void destructuringWithBaseReachedThroughAMapAndAnAliasForDestruct(){ ok(Map.of(), Map.of("bb", "base"), """
use bb.Destruct as D;
"""+pq+"""
B:{ .m({.x, .y}:P):P -> x; .k(d:D):D -> d }
"""); }
  @Test void destructuringNextToADeclaredTypeNamedDestruct(){ ok(Map.of(), Map.of(), pq+"""
Destruct:{}
B:{ .m({.x, .y}:P):P -> x; .k(d:Destruct):Destruct -> d }
"""); }
  @Test void baseTypesThroughAMapAndAnAlias(){ ok(Map.of(), Map.of("bb", "base"), """
use bb.Str as S;
B:{ .m(x:S):S -> x; .v:bb.Void -> {} }
"""); }
  @Test void aliasAndQualifiedNamesThroughTheSameMap(){ ok(Map.of("c", "A:{} A2:{}"), Map.of("a", "c"), """
use a.A as X;
B:{ .m(x:X):X -> x; .k(y:a.A2):a.A2 -> y }
"""); }
  @Test void baseByItsRealNameWhenAMapRenamesIt(){ fail("""
In file: [###].fear

001| B:{ .v:base.Void -> {} }
   |        ^^^^^^^^^

While inspecting a type name
Source code inside folders named "_b" cannot use package name "base".
Did you mean "bb" ?
Visible package names: "bb".
Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), Map.of("bb", "base"), """
B:{ .v:base.Void -> {} }
"""); }
  @Test void numberWithBaseReachedThroughAMap(){ fail("""
In file: [###].fear

001| B:{ .m:B -> 5 }
   |     --------^

While inspecting object literal instance of "bb.Nat" > ".m" line 1
The body of method ".m" of type declaration "B" is an expression returning "iso bb.Nat".
Object literal is of type "bb.Nat" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m:B->5}
Error 8 TypeError""", Map.of(), Map.of("bb", "base"), """
B:{ .m:B -> 5 }
"""); }
  @Test void methodOfANumberWithBaseReachedThroughAMap(){ fail("""
In file: [###].fear

001| B:{ .m:B -> 5.foo }
   |     --------~^^^^

While inspecting ".m" line 1
This call to method ".foo" cannot typecheck.
Method ".foo" is not declared on type "bb.Nat".

Available methods on type "bb.Nat":
-       *(bb.Nat):bb.Nat
-       +(bb.Nat):bb.Nat

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
5.foo
Error 8 TypeError""",Map.of(), Map.of("bb", "base"), """
B:{ .m:B -> 5.foo }
"""); }
  static final String sealedC= "S:base.Sealed{ .m:S }";
  @Test void sealedTypeThroughAMap(){ fail("""
In file: [###].fear

001| B:a.S{ .m -> this }
   | ^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Type declaration "B" implements sealed type "a.S".
Sealed types can only be implemented in their own package.
Type declaration "B" is in package "b".
Type "a.S" is in package "a".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", sealedC), Map.of("a", "c"), """
B:a.S{ .m -> this }
"""); }
  @Test void sealedTypeThroughAMapAndAnAlias(){ fail("""
In file: [###].fear

002| B:X{ .m -> this }
   | ^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Type declaration "B" implements sealed type "X".
Sealed types can only be implemented in their own package.
Type declaration "B" is in package "b".
Type "X" is in package "a".

Name "X" stands for "a.S" because of "use a.S as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", sealedC), Map.of("a", "c"), """
use a.S as X;
B:X{ .m -> this }
"""); }
  @Test void sealedTypeUsedAsAnExpressionThroughAMap(){ fail("""
In file: [###].fear

001| B:{ .k:a.S -> a.S }
   |     ----------^^^

While inspecting object literal instance of "iso a.S" > ".k" line 1
This object literal is missing a required method.
Missing: "imm .m".
Required by: "a.S".
Sealed types can only be implemented in their own package.
Type "a.S" is in package "a".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso -.S
Error 8 TypeError""",Map.of("c", sealedC), Map.of("a", "c"), """
B:{ .k:a.S -> a.S }
"""); }
  @Test void undeclaredSimpleNameSuggestsTheMappedName(){ fail("""
In file: [###].fear

001| B:{.m(x:Server):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "b" and is not made visible via "use".
In scope: "B".
Did you mean "a.Server" ?
Add a "use" or write the full type name.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}"), Map.of("a", "c"), """
B:{.m(x:Server):B->this}
"""); }
  @Test void undeclaredSimpleNameSuggestsTheAlias(){ fail("""
In file: [###].fear

002| B:{.m(x:Server):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "b" and is not made visible via "use".
In scope: "B", "Remote".
Did you mean "Remote" ?

Name "Remote" stands for "a.Server" because of "use a.Server as Remote".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}"), Map.of("a", "c"), """
use a.Server as Remote;
B:{.m(x:Server):B->this}
"""); }
  @Test void undeclaredQualifiedNameSuggestsTheAlias(){ fail("""
In file: [###].fear

002| B:{.m(x:a.Serve):B->this}
   |         ^^^^^^^^

While inspecting a type name
Type "Serve" is not declared in package "a".
Did you mean "Remote" ?
In scope: "Remote".

Name "Remote" stands for "a.Server" because of "use a.Server as Remote".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}"), Map.of("a", "c"), """
use a.Server as Remote;
B:{.m(x:a.Serve):B->this}
"""); }
  @Test void undeclaredQualifiedNameListsTheAliasInScope(){ fail("""
In file: [###].fear

002| B:{.m(x:a.Z):B->this}
   |         ^^^^

While inspecting a type name
Type "Z" is not declared in package "a".
In scope: "X".

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:a.Z):B->this}
"""); }
  @Test void wrongPackageSuggestsTheAliasOfTheSameSimpleName(){ fail("""
In file: [###].fear

002| B:{.m(x:d.Server):B->this}
   |         ^^^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "d".
In scope: "d.Client".
Did you mean "Remote" ?

Name "Remote" stands for "a.Server" because of "use a.Server as Remote".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}", "d", "Client:{}"), Map.of("a", "c"), """
use a.Server as Remote;
B:{.m(x:d.Server):B->this}
"""); }
  @Test void wrongPackageSuggestsTheOwnSimpleName(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Server):B->this}
   |         ^^^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "a".
In scope: "a.A".
Did you mean "Server" ?

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:a.Server):B->this}
Server:{}
"""); }
  @Test void wrongPackageSuggestsTheMappedName(){ fail("""
In file: [###].fear

001| B:{.m(x:d.Server):B->this}
   |         ^^^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "d".
In scope: "d.Client".
Did you mean "a.Server" ?
Add a "use" or write the full type name.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}", "d", "Client:{}"), Map.of("a", "c"), """
B:{.m(x:d.Server):B->this}
"""); }
  static final String cBox= "A:{.fromC:A->this} D:{} Box[T]:{.get:T; .put(t:T):Box[T]->this}";
  @Test void callResultWithAMappedTypeArgument(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Box[a.A]):B->x.get}
   |    --------------------^^^^^^

While inspecting method call ".get" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "a.A".
Method call "a.Box[_].get" has type "a.A" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.Box[-.A]):B->x.get}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:a.Box[a.A]):B->x.get}
"""); }
  @Test void callResultWithAnOwnTypeAsTheArgumentOfAMappedType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Box[B]):a.A->x.get}
   |    --------------------^^^^^^

While inspecting method call ".get" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "B".
Method call "a.Box[_].get" has type "B" instead of a subtype of "a.A".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "a.A" was introduced: (compression indicated by `-`)
B:{.m(x:-.Box[B]):-.A->x.get}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:a.Box[B]):a.A->x.get}
"""); }
  @Test void callResultWithAnAliasAsTheArgumentOfAMappedType(){ fail("""
In file: [###].fear

002| B:{.m(x:a.Box[X]):B->x.get}
   |    ------------------^^^^^^

While inspecting method call ".get" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "B" is an expression returning "X".
Method call "a.Box[_].get" has type "X" instead of a subtype of "B".

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.Box[X]):B->x.get}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:a.Box[X]):B->x.get}
"""); }
  @Test void callResultWithTwoAliasesThroughTheSameMap(){ fail("""
In file: [###].fear

003| B:{.m(x:Bx[X]):B->x.get}
   |    ---------------^^^^^^

While inspecting method call ".get" > ".m(_)" line 3
The body of method ".m(_)" of type declaration "B" is an expression returning "X".
Method call "Bx[_].get" has type "X" instead of a subtype of "B".

Name "X" stands for "a.A" because of "use a.A as X".
Name "Bx" stands for "a.Box" because of "use a.Box as Bx".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:Bx[X]):B->x.get}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
use a.Box as Bx;
use a.A as X;
B:{.m(x:Bx[X]):B->x.get}
"""); }
  @Test void aliasedTypeWrittenQualifiedAsATypeArgument(){ fail("""
In file: [###].fear

002| B:{.m(x:a.Box[a.A]):B->this}
   |               ^^^^

While inspecting a type name
The full type name "a.A" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "X" to refer to "a.A", because of "use a.A as X".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:a.Box[a.A]):B->this}
"""); }
  @Test void mapTargetWrittenAsATypeArgument(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Box[c.A]):B->this}
   |               ^^^^

While inspecting a type name
Source code inside folders named "_b" cannot use package name "c".
Did you mean "a" ?
Visible package names: "a", "base".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:a.Box[c.A]):B->this}
"""); }
  @Test void mappedGenericTypesWithAliasesAndOwnTypes(){ ok(Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:a.Box[X]):X->x.get.fromC; .k(y:a.Box[X], z:X):a.Box[X]->y.put(z); .own(b:a.Box[B]):B->b.get}
"""); }
  static final Map<String,String> webVersions= Map.of("web_v1", "Server:{.v1:Server->this}", "web_v2", "Server:{.v2:Server->this}");
  static final Map<String,String> legacyAndWeb= Map.of("legacy", "web_v1", "web", "web_v2");
  @Test void anAliasAndAMapForTwoVersionsOfAPackage(){ ok(webVersions, legacyAndWeb, """
use legacy.Server as OldServer;
B:{.m(x:OldServer, y:web.Server):web.Server->y.v2; .k(x:OldServer):OldServer->x.v1}
"""); }
  @Test void anAliasAndAMapForTwoVersionsDisagree(){ fail("""
In file: [###].fear

002| B:{.m(x:OldServer):web.Server->x}
   |    ----------------------------^^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "B" is an expression returning "OldServer".
Parameter "x" has type "OldServer" instead of a subtype of "web.Server".

Name "OldServer" stands for "legacy.Server" because of "use legacy.Server as OldServer".
Source code inside folders named "_b" uses package name "legacy" to refer to the code inside folders named "_web_v1", because of "map legacy as _web_v1 in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "web" to refer to the code inside folders named "_web_v2", because of "map web as _web_v2 in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "web.Server" was introduced: (compression indicated by `-`)
B:{.m(x:OldServer):-.Server->x}
Error 8 TypeError""", webVersions, legacyAndWeb, """
use legacy.Server as OldServer;
B:{.m(x:OldServer):web.Server->x}
"""); }
  @Test void aMethodOfTheOtherVersionThroughAnAlias(){ fail("""
In file: [###].fear

002| B:{.m(x:OldServer, y:web.Server):web.Server->x.v2}
   |    ------------------------------------------~^^^^

While inspecting ".m(_,_)" line 2
This call to method ".v2" cannot typecheck.
Method ".v2" is not declared on type "OldServer".
Did you mean ".v1" ?

Available methods on type "OldServer":
-       .v1:OldServer

Name "OldServer" stands for "legacy.Server" because of "use legacy.Server as OldServer".
Source code inside folders named "_b" uses package name "legacy" to refer to the code inside folders named "_web_v1", because of "map legacy as _web_v1 in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.v2
Error 8 TypeError""", webVersions, legacyAndWeb, """
use legacy.Server as OldServer;
B:{.m(x:OldServer, y:web.Server):web.Server->x.v2}
"""); }
  @Test void methodNotDeclaredOnAQualifiedMappedType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):a.A->x.nope}
   |    ---------------~^^^^^^

While inspecting ".m(_)" line 1
This call to method ".nope" cannot typecheck.
Method ".nope" is not declared on type "a.A".

Available methods on type "a.A":
-       .fromC:a.A

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.nope
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:a.A):a.A->x.nope}
"""); }
  @Test void readMappedTypeWhereMutIsRequired(){ fail("""
In file: [###].fear

001| B:{.m(x:read a.A):mut a.A->x}
   |    ------------------------^^

While inspecting parameter "x" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "read a.A".
Parameter "x" has type "read a.A" instead of a subtype of "mut a.A".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "mut a.A" was introduced: (compression indicated by `-`)
B:{.m(x:read -.A):mut -.A->x}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:read a.A):mut a.A->x}
"""); }
  @Test void mutAndReadMappedTypes(){ ok(Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.k(x:mut X):read X->x; .j(x:mut a.Box[X]):read a.Box[X]->x; .d(x:mut a.D):read a.D->x}
"""); }
  @Test void argumentOfTheWrongMappedType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Box[a.A], d:a.D):a.Box[a.A]->x.put(d)}
   |    ------------------------------------~^^^^^~~

While inspecting ".m(_,_)" line 1
This call to method "a.Box[_].put(_)" cannot typecheck.
Argument 1 has type "a.D".
That is not a subtype of "a.A" (the type required by the method signature).

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
-.put(d)
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:a.Box[a.A], d:a.D):a.Box[a.A]->x.put(d)}
"""); }
  @Test void argumentOfTheWrongAliasedType(){ fail("""
In file: [###].fear

002| B:{.m(x:a.Box[X], d:a.D):a.Box[X]->x.put(d)}
   |    --------------------------------~^^^^^~~

While inspecting ".m(_,_)" line 2
This call to method "a.Box[_].put(_)" cannot typecheck.
Argument 1 has type "a.D".
That is not a subtype of "X" (the type required by the method signature).

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
-.put(d)
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:a.Box[X], d:a.D):a.Box[X]->x.put(d)}
"""); }
  @Test void nestedObjectLiteralOfAMappedType(){ fail("""
In file: [###].fear

001| B:{.m:a.A->a.A{.fromC->base.Void}}
   |    ------------~~~~~~~~^^^^^^^^^^

While inspecting object literal instance of "base.Void" > ".fromC" line 1 > ".m" line 1
Method ".fromC" inside the object literal instance of "iso a.A" (line 1)
is implemented with an expression returning "iso base.Void".
Object literal is of type "base.Void" instead of a subtype of "a.A".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "a.A" was introduced: (compression indicated by `-`)
B:{.m:-.A->-.A{.fromC:-.A->-.Void}}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m:a.A->a.A{.fromC->base.Void}}
"""); }
  @Test void literalMissingTheMethodOfAMappedGenericType(){ fail("""
In file: [###].fear

001| B:{.m:a.Box[a.A]->{}}
   |    ---------------^^

While inspecting object literal instance of "iso a.Box[a.A]" > ".m" line 1
This object literal is missing a required method.
Missing: "imm .get".
Required by: "a.Box[_]".
Hint: add an implementation for ".get" inside the object literal.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso -.Box[-.A]
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m:a.Box[a.A]->{}}
"""); }
  @Test void stringWithBaseReachedThroughAMap(){ fail("""
In file: [###].fear

001| B:{ .m:B -> "hi" }
   |     --------^^^^

While inspecting object literal instance of "bb.Str" > ".m" line 1
The body of method ".m" of type declaration "B" is an expression returning "iso bb.Str".
Object literal is of type "bb.Str" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m:B->"hi"}
Error 8 TypeError""", Map.of(), Map.of("bb", "base"), """
B:{ .m:B -> "hi" }
"""); }
  @Test void numberWithAnAliasForNatThroughAMap(){ fail("""
In file: [###].fear

002| B:{ .m:B -> 5 }
   |     --------^

While inspecting object literal instance of "N" > ".m" line 2
The body of method ".m" of type declaration "B" is an expression returning "iso N".
Object literal is of type "N" instead of a subtype of "B".

Name "N" stands for "bb.Nat" because of "use bb.Nat as N".
Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m:B->5}
Error 8 TypeError""", Map.of(), Map.of("bb", "base"), """
use bb.Nat as N;
B:{ .m:B -> 5 }
"""); }
  @Test void signedNumberWithBaseReachedThroughAMap(){ fail("""
In file: [###].fear

001| B:{ .m:bb.Nat -> +5 }
   |     -------------^^

While inspecting object literal instance of "bb.Int" > ".m" line 1
The body of method ".m" of type declaration "B" is an expression returning "iso bb.Int".
Object literal is of type "bb.Int" instead of a subtype of "bb.Nat".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "bb.Nat" was introduced: (compression indicated by `-`)
B:{.m:-.Nat->+5}
Error 8 TypeError""", Map.of(), Map.of("bb", "base"), """
B:{ .m:bb.Nat -> +5 }
"""); }
  @Test void ownTypeAndMappedTypeWithTheSameSimpleName(){ fail("""
In file: [###].fear

001| B:{.m(x:a.B):B->x}
   |    -------------^^

While inspecting parameter "x" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "a.B".
Parameter "x" has type "a.B" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.B):B->x}
Error 8 TypeError""", Map.of("c", "B:{.fromC:B->this}"), Map.of("a", "c"), """
B:{.m(x:a.B):B->x}
"""); }
  @Test void baseTypeInTheSignatureOfAMappedPackageWhenBaseIsMappedToo(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):B->x.n}
   |    -------------^^^^

While inspecting method call ".n" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "bb.Nat".
Method call "a.A.n" has type "bb.Nat" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.A):B->x.n}
Error 8 TypeError""", Map.of("c", "A:{.n:base.Nat->5}"), Map.of("a", "c", "bb", "base"), """
B:{.m(x:a.A):B->x.n}
"""); }
  @Test void genericMethodCalledWithAMappedTypeArgument(){ fail("""
In file: [###].fear

001| B:{.m(x:a.G, d:a.D):B->x.id[a.D](d)}
   |    --------------------^^^^^^^^^^^^

While inspecting method call ".id(_)" > ".m(_,_)" line 1
The body of method ".m(_,_)" of type declaration "B" is an expression returning "a.D".
Method call "a.G.id(_)" has type "a.D" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.G,d:-.D):B->x.id[imm,-.D](d)}
Error 8 TypeError""", Map.of("c", "D:{} G:{.id[X](x:X):X->x}"), Map.of("a", "c"), """
B:{.m(x:a.G, d:a.D):B->x.id[a.D](d)}
"""); }
  @Test void genericMethodCalledWithAMappedTypeArgumentAndAnAlias(){ ok(Map.of("c", "D:{} G:{.id[X](x:X):X->x}"), Map.of("a", "c"), """
use a.D as Dd;
B:{.m(x:a.G, d:Dd):Dd->x.id[Dd](d); .k(x:a.G, d:Dd):Dd->x.id(d)}
"""); }
  @Test void nestedObjectLiteralOfAnAlias(){ fail("""
In file: [###].fear

002| B:{.m:X->X{.fromC->B}}
   |    --------~~~~~~~~^^

While inspecting object literal instance of "B" > ".fromC" line 2 > ".m" line 2
Method ".fromC" inside the object literal instance of "iso X" (line 2)
is implemented with an expression returning "iso B".
Object literal is of type "B" instead of a subtype of "X".

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
B:{.m:X->X{.fromC:X->B}}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.m:X->X{.fromC->B}}
"""); }
  @Test void literalsWithBaseReachedThroughAMapAndAliases(){ ok(Map.of(), Map.of("bb", "base"), """
use bb.Nat as N;
use bb.Str as S;
B:{ .m:N -> 5; .k(x:N):N -> x+5; .s:S -> "hi"; .i:bb.Int -> +5; .f:bb.Float -> 1.5 }
"""); }
  static final String noteA= "Source code inside folders named \"_b\" uses package name \"a\" to refer to the code inside folders named \"_c\", because of \"map a as _c in _b\", written in fear:/_b/_rank_app.fear.";
  static final String noteBb= "Source code inside folders named \"_b\" uses package name \"bb\" to refer to the code inside folders named \"_base\", because of \"map bb as _base in _b\", written in fear:/_b/_rank_app.fear.";
  @Test void undeclaredSimpleNameSuggestsAnAliasOfAnUnmappedTypeWithNoNote(){ fail("""
In file: [###].fear

002| B:{.m(x:Server):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "b" and is not made visible via "use".
In scope: "B", "Remote".
Did you mean "Remote" ?
Error 7 WellFormedness
""", Map.of("c", cA, "d", "Server:{}"), Map.of("a", "c"), """
use d.Server as Remote;
B:{.m(x:Server):B->this}
"""); }
  @Test void undeclaredSimpleNameSuggestsAnAliasAndAnUnmappedName(){ fail("""
In file: [###].fear

002| B:{.m(x:Server):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "b" and is not made visible via "use".
In scope: "B", "Remote".
Did you mean "Remote" or "d.Server" ?
Add a "use" or write the full type name.

Name "Remote" stands for "a.Server" because of "use a.Server as Remote".
"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", "Server:{}", "d", "Server:{}"), Map.of("a", "c"), """
use a.Server as Remote;
B:{.m(x:Server):B->this}
"""); }
  @Test void undeclaredSimpleNameListsAMappedAliasInScope(){ fail("""
In file: [###].fear

002| B:{.m(x:Qqqqqq):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Qqqqqq" is not declared in package "b" and is not made visible via "use".
In scope: "B", "X".

Name "X" stands for "a.A" because of "use a.A as X".
"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:Qqqqqq):B->this}
"""); }
  @Test void undeclaredQualifiedNameInAMappedBaseSuggestsTheBaseType(){ fail("""
In file: [###].fear

001| B:{.m(x:bb.Strr):B->this}
   |         ^^^^^^^^

While inspecting a type name
Type "Strr" is not declared in package "bb".
Did you mean "bb.Str" ?

"""+noteBb+"""

Error 7 WellFormedness
""", Map.of(), Map.of("bb", "base"), """
B:{.m(x:bb.Strr):B->this}
"""); }
  @Test void undeclaredQualifiedNameInAMappedBaseSuggestsTheAliasOfTheBaseType(){ fail("""
In file: [###].fear

002| B:{.m(x:bb.Strr):B->this}
   |         ^^^^^^^^

While inspecting a type name
Type "Strr" is not declared in package "bb".
Did you mean "S" ?

Name "S" stands for "bb.Str" because of "use bb.Str as S".
"""+noteBb+"""

Error 7 WellFormedness
""", Map.of(), Map.of("bb", "base"), """
use bb.Str as S;
B:{.m(x:bb.Strr):B->this}
"""); }
  @Test void undeclaredSimpleNameSuggestsABaseTypeThroughAMap(){ fail("""
In file: [###].fear

001| B:{.m(x:Str):B->this}
   |         ^^^^

While inspecting a type name
Type "Str" is not declared in package "b" and is not made visible via "use".
In scope: "B".
Did you mean "bb.Str" ?
Add a "use" or write the full type name.

"""+noteBb+"""

Error 7 WellFormedness
""", Map.of(), Map.of("bb", "base"), """
B:{.m(x:Str):B->this}
"""); }
  @Test void undeclaredSimpleNameSuggestsTwoMappedNamesWithTheirNotesInTheOrderShown(){ fail("""
In file: [###].fear

001| B:{.m(x:Server):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "b" and is not made visible via "use".
In scope: "B".
Did you mean "a.Server" or "z.Server" ?
Add a "use" or write the full type name.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_e", because of "map a as _e in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "z" to refer to the code inside folders named "_c", because of "map z as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}", "e", "Server:{}"), Map.of("z", "c", "a", "e"), """
B:{.m(x:Server):B->this}
"""); }
  @Test void currentPackageQualifiedSuggestsAMappedNameWithItsNote(){ fail("""
In file: [###].fear

001| B:{.m(x:b.B):B->this}
   |         ^^^^

While inspecting a type name
The full type name "b.B" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "B" to refer to "b.B".
Did you mean "a.B" ?

"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", "B:{}"), Map.of("a", "c"), """
B:{.m(x:b.B):B->this}
"""); }
  @Test void missingReturnTypeInALiteralOfAMappedTypeNamesTheMapOnlyInTheFrame(){ fail("""
In file: [###].fear

001| B:{ .m:a.A->{ .k->B; }; }
   |             --^^^^^---

While inspecting object literal instance of "a.A"
Missing return type for method ".k".
Add an explicit return type before '->'.
Alternatively (less common), if you intended to override and omit the signature,
the signature must be inherited from a supertype.
Cannot infer signature of method ".k".
No supertype has a method named ".k" with 0 parameters.

"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", "A:{}"), Map.of("a", "c"), """
B:{ .m:a.A->{ .k->B; }; }
"""); }
  @Test void missingReturnTypeInALiteralOfAMappedAliasNamesTheAliasOnlyInTheFrame(){ fail("""
In file: [###].fear

002| B:{ .m:X->{ .k->B; }; }
   |           --^^^^^---

While inspecting object literal instance of "X"
Missing return type for method ".k".
Add an explicit return type before '->'.
Alternatively (less common), if you intended to override and omit the signature,
the signature must be inherited from a supertype.
Cannot infer signature of method ".k".
No supertype has a method named ".k" with 0 parameters.

Name "X" stands for "a.A" because of "use a.A as X".
"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", "A:{}"), Map.of("a", "c"), """
use a.A as X;
B:{ .m:X->{ .k->B; }; }
"""); }
  static final String cIds= "IdRO:{ #[X:imm,read](x:X):X->x } Id:{ #[X:**](x:X):X->x }";
  @Test void argumentMatchingNoPromotionNamesAMappedReceiverOnlyInTheReason(){ fail("""
In file: [###].fear

003| A:{ .f(aaaa:mut A):B->Need#(a.IdRO#[read A](aaaa)); }
   |     ------------------~~~~^^~~~~~~~~~~~~~~~~~~~~~-

While inspecting ".f(_)" line 3
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A".
Method call "a.IdRO#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result)

"""+noteA+"""


See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):B->Need#(-.IdRO#[imm,read A](aaaa))}
Error 8 TypeError""", Map.of("c", cIds), Map.of("a", "c"), """
B:{}
Need:{ #(x:mut A):B->B{} }
A:{ .f(aaaa:mut A):B->Need#(a.IdRO#[read A](aaaa)); }
"""); }
  @Test void argumentMatchingNoPromotionNamesAMappedAliasOnlyInTheReason(){ fail("""
In file: [###].fear

004| A:{ .f(aaaa:mut A):B->Need#(Ro#[read A](aaaa)); }
   |     ------------------~~~~^^~~~~~~~~~~~~~~~~~-

While inspecting ".f(_)" line 4
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A".
Method call "Ro#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result)

Name "Ro" stands for "a.IdRO" because of "use a.IdRO as Ro".
"""+noteA+"""


See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):B->Need#(Ro#[imm,read A](aaaa))}
Error 8 TypeError""", Map.of("c", cIds), Map.of("a", "c"), """
use a.IdRO as Ro;
B:{}
Need:{ #(x:mut A):B->B{} }
A:{ .f(aaaa:mut A):B->Need#(Ro#[read A](aaaa)); }
"""); }
  @Test void promotionsDisagreeNameAMappedReceiverOnlyInThePromotionFailures(){ fail("""
In file: [###].fear

001| A:{ .f(p:read A, q:mut A):A->this; .caller(x:readH A, y:mutH A):A->this.f(a.Id#(x), y); }
   |                                    --------------------------------~~~~^^^~~~~~~~~~~~~

While inspecting ".caller(_,_)" line 1
This call to method ".f(_,_)" cannot typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.

Promotion failures:
- Argument 1 fails:    As declared
  Method call "a.Id#(_)" has type "readH A" instead of a subtype of "read A".
- Argument 1 fails:    Strengthen result, Strengthen hygienic result, Allow mutH receiver, Allow mutH argument 2
  Method call "a.Id#(_)" has type "readH A" instead of a subtype of "A".
- Argument 2 fails:    Allow readH arguments, Allow mutH argument 1
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

"""+noteA+"""


Compressed relevant code with inferred types: (compression indicated by `-`)
this.f(-.Id#[imm,read A](x),y)
Error 8 TypeError""", Map.of("c", cIds), Map.of("a", "c"), """
A:{ .f(p:read A, q:mut A):A->this; .caller(x:readH A, y:mutH A):A->this.f(a.Id#(x), y); }
"""); }
  @Test void twoMapsInOneTypeErrorGiveTwoNotesInTheOrderTheNamesArePrinted(){ fail("""
In file: [###].fear

001| B:{.m(x:z.A):a.A->x}
   |    ---------------^^

While inspecting parameter "x" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "z.A".
Parameter "x" has type "z.A" instead of a subtype of "a.A".

Source code inside folders named "_b" uses package name "z" to refer to the code inside folders named "_c", because of "map z as _c in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_e", because of "map a as _e in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "a.A" was introduced: (compression indicated by `-`)
B:{.m(x:-.A):-.A->x}
Error 8 TypeError""", Map.of("c", cA, "e", aA), Map.of("z", "c", "a", "e"), """
B:{.m(x:z.A):a.A->x}
"""); }
  @Test void aliasesOfAMappedAndOfAnUnmappedTypeNoteOnlyTheMappedOne(){ fail("""
In file: [###].fear

003| B:{.m(x:Dd):X->x}
   |    ------------^^

While inspecting parameter "x" > ".m(_)" line 3
The body of method ".m(_)" of type declaration "B" is an expression returning "Dd".
Parameter "x" has type "Dd" instead of a subtype of "X".

Name "X" stands for "a.A" because of "use a.A as X".
"""+noteA+"""


See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
B:{.m(x:Dd):X->x}
Error 8 TypeError""", Map.of("c", cA, "d", dA), Map.of("a", "c"), """
use d.A as Dd;
use a.A as X;
B:{.m(x:Dd):X->x}
"""); }
  @Test void twoAliasesThroughTwoMapsGiveTheNameNotesFirst(){ fail("""
In file: [###].fear

003| B:{.m(x:Y):X->x}
   |    -----------^^

While inspecting parameter "x" > ".m(_)" line 3
The body of method ".m(_)" of type declaration "B" is an expression returning "Y".
Parameter "x" has type "Y" instead of a subtype of "X".

Name "Y" stands for "z.A" because of "use z.A as Y".
Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "z" to refer to the code inside folders named "_e", because of "map z as _e in _b", written in fear:/_b/_rank_app.fear.
"""+noteA+"""


See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
B:{.m(x:Y):X->x}
Error 8 TypeError""", Map.of("c", cA, "e", dA), Map.of("a", "c", "z", "e"), """
use a.A as X;
use z.A as Y;
B:{.m(x:Y):X->x}
"""); }
  @Test void packageNamesAsAndInThroughMaps(){ ok(Map.of("c", cA, "d", dA), Map.of("as", "c", "in", "d"), """
map as as _c in _b;
map in as _d in _b;
B:{.m(x:as.A, y:in.A):as.A->x.fromC; .n(y:in.A):in.A->y.fromD}
"""); }
  @Test void packageNamesInsteadAndOfThroughMapsWithAnInsteadOfList(){ ok(Map.of("c", cA, "d", dA), Map.of("instead", "c", "of", "d"), """
map instead as _c in _b instead of _instead, _of;
map of as _d in _b instead of _instead;
use of.A as OfA;
B:{.m(x:instead.A, y:OfA):OfA->y.fromD}
"""); }
  @Test void packageNamesMapAndUseThroughMaps(){ ok(Map.of("c", cA, "d", dA), Map.of("map", "c", "use", "d"), """
map map as _c in _b;
map use as _d in _b;
use map.A as M;
B:{.m(x:M, y:use.A):use.A->y.fromD; .k(x:M):M->x.fromC}
"""); }
  @Test void aParameterNamedLikeTheMappedPackage(){ ok(Map.of("c", cA), Map.of("a", "c"), """
B:{.m(a:a.A):a.A->a.fromC; .k(as:a.A):a.A->as.fromC}
"""); }
  @Test void aFolderNameWithExtraUnderscores(){ ok(Map.of("c__v_", cA), Map.of("a", "c__v_"), """
map a as _c__v_ in _b instead of _c__v4_;
B:{.m(x:a.A):a.A->x.fromC}
"""); }
  @Test void aFolderNameWithExtraUnderscoresWrittenByItsOwnName(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):c__v_.A->x.fromC}
   |              ^^^^^^^^

While inspecting a type name
Source code inside folders named "_b" cannot use package name "c__v_".
Did you mean "a" ?
Visible package names: "a", "base".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c__v_", because of "map a as _c__v_ in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c__v_", cA), Map.of("a", "c__v_"), """
B:{.m(x:a.A):c__v_.A->x.fromC}
"""); }
  @Test void aKeywordLikeMapTargetWrittenByItsOwnName(){ fail("""
In file: [###].fear

001| B:{.m(x:as.A):in.A->x.fromC}
   |               ^^^^^

While inspecting a type name
Source code inside folders named "_b" cannot use package name "in".
Did you mean "as" ?
Visible package names: "as", "base".
Source code inside folders named "_b" uses package name "as" to refer to the code inside folders named "_in", because of "map as as _in in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("in", cA), Map.of("as", "in"), """
B:{.m(x:as.A):in.A->x.fromC}
"""); }
  @Test void useOfAKeywordLikeMappedNameToAMissingType(){ fail("""
In file: [###].fear

001| use of.Z as Z;
   |     ^^^^

While inspecting package header
"use" directive refers to type "Z", which is not declared in package "of".

Source code inside folders named "_b" uses package name "of" to refer to the code inside folders named "_c", because of "map of as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("of", "c"), """
use of.Z as Z;
B:{}
"""); }
  @Test void useOfASimpleNameNextToAMap(){ fail("""
In file: [###].fear

001| use A as X;
   |     ^

While inspecting package header
"use" directive refers to "A", which is not a full type name.
A "use" directive refers to a type of another package by its full type name, as in "use base.Str as Str;".
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use A as X;
B:{.m(x:a.A):a.A->x.fromC}
"""); }
  @Test void undeclaredSimpleNameThroughAKeywordLikeMap(){ fail("""
In file: [###].fear

001| B:{.m(x:A):B->this}
   |         ^^

While inspecting a type name
Type "A" is not declared in package "b" and is not made visible via "use".
In scope: "B".
Did you mean "in.A" ?
Add a "use" or write the full type name.

Source code inside folders named "_b" uses package name "in" to refer to the code inside folders named "_c", because of "map in as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("in", "c"), """
B:{.m(x:A):B->this}
"""); }
  @Test void literalsWithBaseMappedToAKeywordLikeName(){ ok(Map.of(), Map.of("in", "base"), """
B:{ .m:in.Nat -> 5; .s:in.Str -> "hi"; .i:in.Int -> +5 }
"""); }
  @Test void reservedLookingButValidNamesInAMapLine(){ ok(Map.of("c", cA), Map.of("con1", "c"), """
map con1 as _com0 in _lpt10 instead of _nul_, _aux2;
B:{.m(x:con1.A):con1.A->x.fromC}
"""); }
  @Test void aReservedFolderNameInAMapLine(){ fail("""
In file: [###].fear

001| map a as _com1 in _b;
   | ~~~~~~~~~^^^^^~~~~~~-
002| B:{}

While inspecting header element > file header > full file
Missing folder name.
Found instead: "_com1".
Expected: "folder name: the _ symbol followed by a package name".
Error 2 UnexpectedToken
""", Map.of(), Map.of(), """
map a as _com1 in _b;
B:{}
"""); }
  @Test void anInsteadOfListWithoutSpacesAndWithComments(){ ok(Map.of("c", cA), Map.of("a", "c"), """
map a as _c /*folder*/ in _b instead of _d,_e //older
  ,_f;
B:{.m(x:a.A):a.A->x.fromC}
"""); }
  @Test void anInsteadOfListWithATrailingComma(){ fail("""
In file: [###].fear

001| map a as _c in _b instead of _d,;
   | ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^-
002| B:{}

While inspecting header element > file header > full file
Missing folder name.
Expected: "folder name: the _ symbol followed by a package name".
Error 2 UnexpectedToken
""", Map.of("c", cA), Map.of("a", "c"), """
map a as _c in _b instead of _d,;
B:{}
"""); }
  @Test void anInsteadOfListWithoutOf(){ fail("""
In file: [###].fear

001| map a as _c in _b instead _d;
   | ~~~~~~~~~~~~~~~~~~~~~~~~~~^^-
002| B:{}

While inspecting header element > file header > full file
Missing "of" keyword.
Found instead: "_d".
Expected: "of".
Error 2 UnexpectedToken
""", Map.of("c", cA), Map.of("a", "c"), """
map a as _c in _b instead _d;
B:{}
"""); }
  @Test void aMapLineWithoutItsSemicolonBeforeADeclaration(){ fail("""
In file: [###].fear

001| map a as _c in _b instead of _d
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
002| B:{}

While inspecting file header > full file
Missing semicolon.
Found instead: "_d".
Expected: ";".
Error 2 UnexpectedToken
""", Map.of("c", cA), Map.of("a", "c"), """
map a as _c in _b instead of _d
B:{}
"""); }
  @Test void aRepeatedMapLineWithKeywordLikeNames(){ fail("""
In file: [###].fear

001| map in as _c in _as;
002| map in as _d in _as instead of _c;
   | -------------------------------^^

While inspecting header element > file header > full file
There is already a map of package name "in" for source code inside folders named "_as".
Error 2 UnexpectedToken
""", Map.of("c", cA), Map.of("in", "c"), """
map in as _c in _as;
map in as _d in _as instead of _c;
B:{}
"""); }
  @Test void aMapLineWithAnUppercaseFolderName(){ fail("""
In file: [###].fear

001| map a as _cC in _b;
   | ~~~~~~~~~^^^~~~~~~-
002| B:{}

While inspecting header element > file header > full file
Missing folder name.
Found instead: "_cC".
Expected: "folder name: the _ symbol followed by a package name".
Error 2 UnexpectedToken
""", Map.of("c", cA), Map.of("a", "c"), """
map a as _cC in _b;
B:{}
"""); }
  static void failBase(String expected, String src){
    var o= oraclePkg(List.of(src));
    var fe= assertThrows(FearlessException.class, () -> new FrontendLogicMain().of("base", Map.of(), o.allFiles(), OtherPackages.empty()));
    strCmp(expected, fe.render(o));
    if (!checkCompact){ return; }
    assertThrows(compact.Frontend.Fail.class, () -> compactAll("base", o, List.of()));
  }
  @Test void compilingBaseWithAMisspelledPackageName(){ failBase("""
In file: [###].fear

002| A:{.m(x:bse.Str):A->this}
   |         ^^^^^^^^

While inspecting a type name
Source code inside folders named "_base" cannot use package name "bse".
Error 7 WellFormedness
""", """
Str:{}
A:{.m(x:bse.Str):A->this}
"""); }
  @Test void compilingBaseWithAMisspelledPackageNameInAMethodBody(){ failBase("""
In file: [###].fear

002| A:{.m:A->bse.A{}}
   |          ^^^^^^

While inspecting a type name
Source code inside folders named "_base" cannot use package name "bse".
Error 7 WellFormedness
""", """
Str:{}
A:{.m:A->bse.A{}}
"""); }
  @Test void compilingBaseWithAUseOfAMissingPackage(){ failBase("""
In file: [###].fear

001| use zz.A as X;
   |     ^^^^

While inspecting package header
Source code inside folders named "_base" cannot use package name "zz".
Error 7 WellFormedness
""", """
use zz.A as X;
Str:{}
"""); }
  static final Map<String,String> jsons= Map.of("json_v1", "Parser:{.v1:Parser->this}", "json_v2", "Parser:{.v2:Parser->this}");
  static final String jsonNote= "Source code inside folders named \"_b\" uses package name \"json\" to refer to the code inside folders named \"_json_v2\", because of \"map json as _json_v2 in _b\", written in fear:/_b/_rank_app.fear.";
  @Test void aHiddenVersionSuggestsTheMapNameOverACloserVersion(){ fail("""
In file: [###].fear

001| B:{.m(x:json_v2.Parser):json.Parser->x.v2}
   |         ^^^^^^^^^^^^^^^

While inspecting a type name
Source code inside folders named "_b" cannot use package name "json_v2".
Did you mean "json" ?
Visible package names: "base", "json", "json_v1".
"""+jsonNote+"""

Error 7 WellFormedness
""", jsons, Map.of("json", "json_v2"), """
B:{.m(x:json_v2.Parser):json.Parser->x.v2}
"""); }
  @Test void aUseOfAHiddenVersionSuggestsTheMapNameOverACloserVersion(){ fail("""
In file: [###].fear

001| use json_v2.Parser as P;
   |     ^^^^^^^^^^^^^^

While inspecting package header
Source code inside folders named "_b" cannot use package name "json_v2".
Did you mean "json" ?
Visible package names: "base", "json", "json_v1".
"""+jsonNote+"""

Error 7 WellFormedness
""", jsons, Map.of("json", "json_v2"), """
use json_v2.Parser as P;
B:{.m(x:P):P->x.v2}
"""); }
  @Test void aMisspelledVersionNotHiddenByAMapSuggestsTheClosestName(){ fail("""
In file: [###].fear

001| B:{.m(x:json_v3.Parser):json.Parser->x.v2}
   |         ^^^^^^^^^^^^^^^

While inspecting a type name
Source code inside folders named "_b" cannot use package name "json_v3".
Did you mean "json_v1" ?
Visible package names: "base", "json", "json_v1".
Error 7 WellFormedness
""", jsons, Map.of("json", "json_v2"), """
B:{.m(x:json_v3.Parser):json.Parser->x.v2}
"""); }
  @Test void bothVersionsReachedThroughOneMapAndOneOwnName(){ ok(jsons, Map.of("json", "json_v2"), """
B:{.m(x:json.Parser, y:json_v1.Parser):json_v1.Parser->y.v1; .k(x:json.Parser):json.Parser->x.v2}
"""); }
  static final String cOver= "P:{} Q:P{} Parent:{ .g(x:P):base.Void } Sup:{ .h:Q }";
  static final Map<String,String> mapA= Map.of("a", "c");
  static final Map<String,String> mapBb= Map.of("bb", "base");
  static final Map<String,String> mapABb= Map.of("a", "c", "bb", "base");
  @Test void sweepTypeArgumentOutOfTheBoundsOfAMappedGenericType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Box[mut B]):B->this}
   | --------^^^^^^^^^^^^----------

While inspecting type declaration "B"
The type "a.Box[mut B]" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "a.Box[_]".
Here "X" can only use capability "imm".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:{.m(x:-.Box[mut B]):B->this}
Error 8 TypeError
""", Map.of("c", "Box[X:imm]:{}"), mapA, """
B:{.m(x:a.Box[mut B]):B->this}
"""); }
  @Test void sweepTypeArgumentOutOfTheBoundsOfAnAliasedGenericType(){ fail("""
In file: [###].fear

002| B:{.m(x:Bx[mut B]):B->this}
   | --------^^^^^^^^^----------

While inspecting type declaration "B"
The type "Bx[mut B]" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "Bx[_]".
Here "X" can only use capability "imm".

Name "Bx" stands for "a.Box" because of "use a.Box as Bx".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:{.m(x:Bx[mut B]):B->this}
Error 8 TypeError
""", Map.of("c", "Box[X:imm]:{}"), mapA, """
use a.Box as Bx;
B:{.m(x:Bx[mut B]):B->this}
"""); }
  @Test void sweepMethodTypeArgumentOutOfTheBoundsOfAMappedMethod(){ fail("""
In file: [###].fear

001| B:{.m(g:a.G, b:mut B):a.G->g#[mut B](b)}
   |    ------------------------^^^^^^^^^^^^

While inspecting method call "#(_)" > ".m(_,_)" line 1
The call to "#(_)" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "a.G#(_)".
Here "X" can only use capability "imm".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
g#[imm,mut B](b)
Error 8 TypeError
""", Map.of("c", "G:{ #[X:imm](x:X):G->this }"), mapA, """
B:{.m(g:a.G, b:mut B):a.G->g#[mut B](b)}
"""); }
  @Test void sweepOverrideAcceptsAMappedParameterOfAStrongerType(){ fail("""
In file: [###].fear

001| B:a.Parent{ .g(x:a.Q):base.Void -> base.Void }
   | ------------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^--

While inspecting type declaration "B"
Invalid method signature overriding for "B.g(_)".
The method ".g(_)" accepts parameter 1 of type "a.Q".
But "a.Parent.g(_)" requires "a.P", which is not a subtype of "a.Q".
It is instead a supertype: you are strengthening the parameter instead of weakening it.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:-.Parent{.g(x:-.Q):-.Void->-.Void}
Error 8 TypeError
""", Map.of("c", cOver), mapA, """
B:a.Parent{ .g(x:a.Q):base.Void -> base.Void }
"""); }
  @Test void sweepOverrideChangesTheCapabilityOfAMappedParameter(){ fail("""
In file: [###].fear

001| B:a.Parent{ .g(x:read a.P):base.Void -> base.Void }
   | ------------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^--

While inspecting type declaration "B"
Invalid method signature overriding for "B.g(_)".
The method ".g(_)" accepts parameter 1 of type "read a.P".
But "a.Parent.g(_)" requires "imm a.P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:-.Parent{.g(x:read -.P):-.Void->-.Void}
Error 8 TypeError
""", Map.of("c", cOver), mapA, """
B:a.Parent{ .g(x:read a.P):base.Void -> base.Void }
"""); }
  @Test void sweepOverrideChangesTheCapabilityOfAMappedResult(){ fail("""
In file: [###].fear

001| B:a.Sup{ .h:read a.Q -> a.Q }
   | ---------^^^^^^^^^^^^^^^^^^--

While inspecting type declaration "B"
Invalid method signature overriding for "B.h".
The method ".h" returns type "read a.Q".
But "a.Sup.h" returns type "imm a.Q".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:-.Sup{.h:read -.Q->-.Q}
Error 8 TypeError
""", Map.of("c", cOver), mapA, """
B:a.Sup{ .h:read a.Q -> a.Q }
"""); }
  @Test void sweepOverrideReturnsAMappedResultOfAWeakerType(){ fail("""
In file: [###].fear

001| B:a.Sup{ .h:a.P -> a.P }
   | ---------^^^^^^^^^^^^^--

While inspecting type declaration "B"
Invalid method signature overriding for "B.h".
The method ".h" returns type "a.P".
But "a.Sup.h" returns type "a.Q", which is not a supertype of "a.P".
It is instead a subtype: you are weakening the result instead of strengthening it.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:-.Sup{.h:-.P->-.P}
Error 8 TypeError
""", Map.of("c", cOver), mapA, """
B:a.Sup{ .h:a.P -> a.P }
"""); }
  @Test void sweepOverrideOfAnAliasedSupertypeReturnsAWeakerType(){ fail("""
In file: [###].fear

002| B:S{ .h:a.P -> a.P }
   | -----^^^^^^^^^^^^^--

While inspecting type declaration "B"
Invalid method signature overriding for "B.h".
The method ".h" returns type "a.P".
But "S.h" returns type "a.Q", which is not a supertype of "a.P".
It is instead a subtype: you are weakening the result instead of strengthening it.

Name "S" stands for "a.Sup" because of "use a.Sup as S".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:S{.h:-.P->-.P}
Error 8 TypeError
""", Map.of("c", cOver), mapA, """
use a.Sup as S;
B:S{ .h:a.P -> a.P }
"""); }
  @Test void sweepTypeDeclaredInAMethodWithBaseReachedThroughAMap(){ fail("""
In file: [###].fear

003| U:{ .m:A -> Foo:A{'s .k -> s; .v -> G#(s, {}) } }
   |     --------------------------~~~~~~~~~~~~^^~--

While inspecting object literal instance of "Foo" > ".v" line 3 > ".m" line 3
The type "Foo" is not standalone: it is declared inside a method body.
Only a standalone type can be extended or mentioned by name.
A type is standalone if it is declared at top level, or if it implements "bb.CaptureFree".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
Foo
Error 8 TypeError
""", Map.of(), mapBb, """
G:{ #[X:*](a:X, b:X):bb.Void -> bb.Void }
A:{ .k:A; .v:bb.Void }
U:{ .m:A -> Foo:A{'s .k -> s; .v -> G#(s, {}) } }
"""); }
  @Test void sweepDeadMutMethodInALiteralOfAMappedType(){ fail("""
In file: [###].fear

001| B:{ mut .baz(m:mut a.M):read a.M -> { .bar -> m } }
   |     --------------------------------~~^^^^^^^^^~~

While inspecting object literal instance of "read a.M" > ".baz(_)" line 1
The method "mut a.M.bar" is dead code.
The object literal instance of "a.M" is "read", so it will never be seen as "mut".
But it implements method "mut .bar", which requires a "mut" receiver.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
read -.M{mut .bar:mut -.M->m}
Error 8 TypeError
""", Map.of("c", "M:{ mut .bar:mut M }"), mapA, """
B:{ mut .baz(m:mut a.M):read a.M -> { .bar -> m } }
"""); }
  @Test void sweepDeadSelfNameInALiteralOfAMappedType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):a.A->a.A{'s .fromC -> x}}
   |    ---------------^^^^---------------

While inspecting object literal instance of "a.A" > ".m(_)" line 1
The self name "s" is dead code.
No method of the object literal instance of "a.A" uses it.
Remove "'s" from the object literal.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
-.A{'s .fromC:-.A->x}
Error 8 TypeError
""", Map.of("c", cA), mapA, """
B:{.m(x:a.A):a.A->a.A{'s .fromC -> x}}
"""); }
  @Test void sweepIsoUsedTwiceInALiteralOfAMappedType(){ fail("""
In file: [###].fear

001| B:{.k:a.F -> a.F{ .m(x) -> a.Use2#(x, x) }}
   |                   -----------------^^~~~

While inspecting ".m(_)" line 1 > ".k" line 1
Iso parameter "x" violates the single-use rule in method "a.F.m(_)" (line 1).
It is used directly 2 times.
Iso parameters can be used directly at most once.
Allowed: capture into object literals as "imm", or use directly once.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
-.Use2#(x,x)
Error 8 TypeError
""", Map.of("c", "D:{} F:{ .m(x:iso D):D } Use2:{ #(a:iso D, b:iso D):D -> a }"), mapA, """
B:{.k:a.F -> a.F{ .m(x) -> a.Use2#(x, x) }}
"""); }
  @Test void sweepMutCapturedInAnImmLiteralOfAMappedType(){ fail("""
In file: [###].fear

001| B:{ .m(x:mut a.D):a.G -> a.G{ # -> a.Ignore#(x) } }
   |     --------------------------~~~~~~~~~~~~~~~^^--

While inspecting parameter "x" > "#" line 1 > ".m(_)" line 1
Parameter "x" has type "mut a.D".
Parameter "x" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "a.G" (line 1).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
x
Error 8 TypeError
""", Map.of("c", "D:{} G:{ #:base.Void } Ignore:{ #(x:read D):base.Void -> {} }"), mapA, """
B:{ .m(x:mut a.D):a.G -> a.G{ # -> a.Ignore#(x) } }
"""); }
  @Test void sweepCaptureInACaptureFreeLiteralOfAMappedType(){ fail("""
In file: [###].fear

001| B:{ #(d:a.D):a.G -> {d} }
   |     -----------------^^

While inspecting parameter "d" > "#" line 1 > "#(_)" line 1
Object literal instance of "iso a.G" implements "bb.CaptureFree".
Thus parameter "d" (line 1) cannot be captured in this scope.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
d
Error 8 TypeError
""", Map.of("c", "D:{} G:base.CaptureFree{ #:D }"), mapABb, """
B:{ #(d:a.D):a.G -> {d} }
"""); }
  @Test void sweepMethodWithAnotherArityOnAMappedType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):a.A->x.fromC(x)}
   |    ---------------~^^^^^^^~~

While inspecting ".m(_)" line 1
This call to method ".fromC(_)" cannot typecheck.
There is a method ".fromC" on type "a.A",
but with a different number of arguments.
This call supplies 1, but available methods take 0.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.fromC(x)
Error 8 TypeError
""", Map.of("c", cA), mapA, """
B:{.m(x:a.A):a.A->x.fromC(x)}
"""); }
  @Test void sweepMethodWithAnotherCapabilityOnAMappedType(){ fail("""
In file: [###].fear

001| B:{.m(x:mut a.R):a.R->x.go[read]}
   |    -------------------~^^^^~~~~~~

While inspecting ".m(_)" line 1
This call to method ".go" cannot typecheck.
".go" exists on type "a.R", but not with the requested capability.
This call requires the existence of a "read" method.
Available capabilities for this method: "mut".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.go[read]
Error 8 TypeError
""", Map.of("c", "R:{ mut .go:R }"), mapA, """
B:{.m(x:mut a.R):a.R->x.go[read]}
"""); }
  @Test void sweepReceiverTooWeakForAMethodOfAMappedType(){ fail("""
In file: [###].fear

001| B:{.m(x:read a.R):a.R->x.go}
   |    --------------------~^^^^

While inspecting ".m(_)" line 1
This call to method "mut a.R.go" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.go[mut]
Error 8 TypeError
""", Map.of("c", "R:{ mut .go:R }"), mapA, """
B:{.m(x:read a.R):a.R->x.go}
"""); }
  @Test void sweepWrongNumberOfTypeArgumentsForAMethodOfAMappedType(){ fail("""
In file: [###].fear

001| B:{.m(p:a.Pairer):B->p.pair[B](this, this)}
   |    ------------------~^^^^^^~~~~~~~~~~~~~~

While inspecting ".m(_)" line 1
This call to method "a.Pairer.pair(_,_)" cannot typecheck.
Wrong number of generic type arguments for ".pair(_,_)".
This method expects 2 generic type arguments: "X" and "Y"; but this call provides 1 generic type argument.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
p.pair[imm,B](this,this)
Error 8 TypeError
""", Map.of("c", "Pairer:{ .pair[X,Y](x:X, y:Y):X -> x }"), mapA, """
B:{.m(p:a.Pairer):B->p.pair[B](this, this)}
"""); }
  @Test void sweepReadLiteralOfAMappedTypeWhereMutIsRequiredHintsTheCapability(){ fail("""
In file: [###].fear

001| B:{.f:a.D->a.Need#(read a.A2{})}
   |    --------~~~~~~^^~~~~~~~~~~--

While inspecting ".f" line 1
This call to method "a.Need#(_)" cannot typecheck.
Argument 1 has type "read a.A2".
That is not a subtype of any of "mut a.A2" or "iso a.A2".
Object literal is of type "read a.A2" instead of a subtype of "mut a.A2".
Hint: write "mut a.A2" if you need a "mut" object literal.

Type required by each promotion:
- "mut a.A2"  (As declared)
- "iso a.A2"  (Strengthen result)

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "mut a.A2" was introduced: (compression indicated by `-`)
B:{.f:-.D->-.Need#(read -.A2)}
Error 8 TypeError
""", Map.of("c", "D:{} A2:{ mut .foo:A2 } Need:{ #(x:mut A2):D -> D }"), mapA, """
B:{.f:a.D->a.Need#(read a.A2{})}
"""); }
  @Test void sweepCaptureAdaptationTraceOfAMappedType(){ fail("""
In file: [###].fear

001| B:{ read .m(x:mut a.D):mut a.D -> read a.Get{ x } }
   |     ------------------------------------------^--

While inspecting parameter "x" > ".get" line 1 > ".m(_)" line 1
Method ".get" inside the object literal instance of "read a.Get" (line 1)
is implemented with an expression returning "read a.D".
Parameter "x" has type "read a.D" instead of a subtype of "mut a.D".
Note: the declared type "mut a.D" would instead be a valid subtype.
Capture adaptation trace:
"mut a.D" --setToRead(line 1)--> "read a.D".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "mut a.D" was introduced: (compression indicated by `-`)
B:{read .m(x:mut -.D):mut -.D->read -.Get{read .get:mut -.D->x}}
Error 8 TypeError
""", Map.of("c", "D:{} Get:{ read .get:mut D }"), mapA, """
B:{ read .m(x:mut a.D):mut a.D -> read a.Get{ x } }
"""); }
  @Test void sweepBaseIdBadBodyWithBaseReachedThroughAMap(){ fail("""
In file: [###].fear

001| I:bb.BaseId[I,I]{ #(x) -> this }
   |                           ^^^^

While inspecting the file
Type declaration "I" implements "bb.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
this
Error 8 TypeError
""", Map.of(), mapBb, """
I:bb.BaseId[I,I]{ #(x) -> this }
"""); }
  @Test void sweepNameClashOfAMappedAlias(){ fail("""
In file: [###].fear

002| A:{}
   | ^^

While inspecting a type name
Name clash: name "A" is declared in package "b".
Name "A" is also used in a "use" directive.
Error 7 WellFormedness
""", Map.of("c", cA), mapA, """
use a.A as A;
A:{}
"""); }
  @Test void sweepTypeParameterNamedLikeAMappedAlias(){ fail("""
In file: [###].fear

002| B:{ .m[X](x:X):X -> x }
   |        ^

While inspecting a type name
Generic type parameter "X" is declared in package "b".
Name "X" is also used in a "use" directive.
Error 7 WellFormedness
""", Map.of("c", cA), mapA, """
use a.A as X;
B:{ .m[X](x:X):X -> x }
"""); }
  @Test void sweepDuplicatedMappedSupertype(){ fail("""
In file: [###].fear

001| B:a.A,a.A{}
   | ^^^^^^^^^^^

While inspecting type declaration "B"
Duplicate supertype in type declaration: "a.A".
Remove one of them.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), mapA, """
B:a.A,a.A{}
"""); }
  @Test void sweepDuplicatedMappedSupertypeWithAndWithoutDefaultImm(){ fail("""
In file: [###].fear

001| B:a.Box[a.A],a.Box[imm a.A]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Duplicate supertype in type declaration: "a.Box[a.A]" and "a.Box[imm a.A]" denote the same type.
Remove one of them.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cBox), mapA, """
B:a.Box[a.A],a.Box[imm a.A]{}
"""); }
  @Test void sweepDuplicatedAliasedSupertype(){ fail("""
In file: [###].fear

002| B:X,X{}
   | ^^^^^^^

While inspecting type declaration "B"
Duplicate supertype in type declaration: "X".
Remove one of them.

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), mapA, """
use a.A as X;
B:X,X{}
"""); }
  @Test void sweepParameterDisagreementBetweenMappedSupertypes(){ fail("""
In file: [###].fear

001| B:a.A1,a.A2{}
   | ^^^^^^^^^^^^^

While inspecting type declaration "B"
Type disagreement about parameter 1 for method "imm .m(_)" with 1 parameter.
Different options are present in the implemented types.
Candidates: "a.P", "a.Q".
Type declaration "B" must declare a method ".m(_)" explicitly choosing the desired option.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "P:{} Q:{} A1:{ .m(x:P):P } A2:{ .m(x:Q):P }"), mapA, """
B:a.A1,a.A2{}
"""); }
  @Test void sweepCapabilityDisagreementBetweenMappedSupertypes(){ fail("""
In file: [###].fear

001| B:a.A1,a.A2{}
   | ^^^^^^^^^^^^^

While inspecting type declaration "B"
Return type disagreement for method "imm .m" with 0 parameters.
Different options are present in the implemented types.
Candidates: "imm a.P", "mut a.P".
They differ in reference capability, and an overriding method must keep it, so no method ".m" can implement all of them.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "P:{} A1:{ .m:P } A2:{ .m:mut P }"), mapA, """
B:a.A1,a.A2{}
"""); }
  @Test void sweepGenericArityOfALiteralOfAMappedType(){ fail("""
In file: [###].fear

001| B:{ .k:a.Sup -> a.Sup{ .f[X,Y](x:X):base.Void -> base.Void } }
   |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "a.Sup"
Invalid method implementation for "a.Sup.f(_)".
The method ".f(_)" declares 2 generic type parameters, but supertypes declare 1.
Local declaration: "[X:imm, Y:imm]".
From supertypes: "[-:imm]".
Change the local number of generic type parameters to 1, or adjust the supertypes.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Sup:{ .f[X](x:X):base.Void }"), mapA, """
B:{ .k:a.Sup -> a.Sup{ .f[X,Y](x:X):base.Void -> base.Void } }
"""); }
  @Test void sweepGenericBoundsOfALiteralOfAMappedType(){ fail("""
In file: [###].fear

001| B:{ .k:a.Sup -> a.Sup{ .id[X:imm,read](x:X):base.Void -> base.Void } }
   |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "a.Sup"
Invalid method implementation for "a.Sup.id(_)".
The local declaration uses different capability bounds than the supertypes for generic type parameter 1 of ".id(_)".
Local: "X:imm,read".
From supertypes: "-:imm".
The parameter name may differ; only the position matters.
Change the local bounds to match the supertypes, or adjust the supertypes.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Sup:{ .id[X:imm](x:X):base.Void }"), mapA, """
B:{ .k:a.Sup -> a.Sup{ .id[X:imm,read](x:X):base.Void -> base.Void } }
"""); }
  @Test void sweepCaptureNotFunnelledWithAMappedGenericType(){ fail("""
In file: [###].fear

001| B:{ read .m[X:imm,mut,read](beer:a.Beer[X]):read Foo -> read Foo:{ read .k:base.Void -> beer.bar } }
   |                                                                                         ^^^^^

While inspecting parameter "beer"
Parameter "beer" has type "a.Beer[X]", using the generic type parameter "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares none.
Hint: funnel "X" into "Foo" by writing "Foo[X:..]", restating the bounds of "X".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Beer[X:imm,mut,read]:{ read .bar:base.Void }"), mapA, """
B:{ read .m[X:imm,mut,read](beer:a.Beer[X]):read Foo -> read Foo:{ read .k:base.Void -> beer.bar } }
"""); }
  @Test void sweepAmbiguousTypeArgumentBetweenMappedTypes(){ fail("""
In file: [###].fear

001| U:{ .both[T](x:T, y:T):a.A -> a.A; .use(y:a.Y, z:a.Z):a.A -> this.both(y, z) }
   |                                                              ^^^^^^^^^^^^^^^

While inspecting method call ".both(_,_)"
The generic type argument "T" of ".both" is inferred from the arguments, but they disagree: some need "a.Y", some need "a.Z".
"T" could be "a.A" or "a.B2": each is a supertype of "a.Y" and "a.Z". The choice is ambiguous.
Write the generic type argument explicitly, as in "this.both[a.A](y, z)".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "A:{} B2:{} Y:A,B2{} Z:A,B2{}"), mapA, """
U:{ .both[T](x:T, y:T):a.A -> a.A; .use(y:a.Y, z:a.Z):a.A -> this.both(y, z) }
"""); }
  @Test void sweepAmbiguousLiteralHeadBetweenMappedTypes(){ fail("""
In file: [###].fear

003| U:{ .use(c:bb.Bool, y:a.Y, z:a.Z):A -> Sink#(c ? { .then -> y; .else -> z }) }
   |                                                  ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "bb.ThenElse[_]"
The generic type argument "R" of "bb.ThenElse[_]" is inferred from the method bodies, but they disagree: some need "a.Y", some need "a.Z".
"R" could be "a.S1" or "a.S2": each is a supertype of "a.Y" and "a.Z". The choice is ambiguous.
Write the generic type argument explicitly, as in "bb.ThenElse[a.S1]{...}".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "S1:{} S2:{} Y:S1,S2{} Z:S1,S2{}"), mapABb, """
A:{}
Sink:{ #[T](t:T):A -> A }
U:{ .use(c:bb.Bool, y:a.Y, z:a.Z):A -> Sink#(c ? { .then -> y; .else -> z }) }
"""); }
  @Test void sweepLiteralHeadOfAMappedTypeNotInferred(){ fail("""
In file: [###].fear

001| B:{ .k:a.T0[base.Void] -> {}.m }
   |                           ^^

While inspecting object literal instance of "a.T0[_]"
Type inference concluded that this object literal implements "a.T0[?]",
but it could not infer generic type argument 1 for generic type parameter "X" of "a.T0[_]".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "T0[X]:{ .m:T0[base.Void] }"), mapA, """
B:{ .k:a.T0[base.Void] -> {}.m }
"""); }
  @Test void sweepTypeGrowsForeverThroughMappedTypes(){ fail("""
In file: [###].fear

001| Use:{ .go:a.N -> a.Take#{ .m(x) -> a.Wrap#(x) } }
   |                         ^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "a.Foo[_]"
Type inference finds no type for object literal instance of "a.Foo[_]".
Each round of inference nests its type one level deeper, as "a.Foo[a.Box[a.Box[...]]]"; it would grow without bound.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "N:{} Box[X]:{} Wrap:{ #[Y](y:Y):Box[Y] -> {} } Foo[X]:{ .m(x:X):X } Take:{ #[Z](f:Foo[Z]):N -> N }"), mapA, """
Use:{ .go:a.N -> a.Take#{ .m(x) -> a.Wrap#(x) } }
"""); }
  @Test void sweepAmbiguousImplementationBetweenMappedSupertypes(){ fail("""
In file: [###].fear

001| B:a.I1,a.I2{}
   | ^^^^^^^^^^^^^

While inspecting type declaration "B"
Ambiguous implementation for method ".m" with 0 parameters.
Different options are present in the implemented types.
Candidates: "a.I1", "a.I2".
Type declaration "B" must declare a method ".m" explicitly implementing the desired behaviour.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "I1:{ .m:base.Void -> base.Void } I2:{ .m:base.Void -> base.Void }"), mapA, """
B:a.I1,a.I2{}
"""); }
  @Test void sweepMultipleWidenToThroughAMap(){ fail("""
In file: [###].fear

001| B:bb.WidenTo[B],bb.WidenTo[a.A]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Type declaration "B" implements "bb.WidenTo[_]" more than once.
At most one "bb.WidenTo[_]" supertype is allowed, because it defines the preferred widened type.

Found the following "bb.WidenTo[_]" supertypes:
- "bb.WidenTo[B]"
- "bb.WidenTo[a.A]"

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), mapABb, """
B:bb.WidenTo[B],bb.WidenTo[a.A]{}
"""); }
  @Test void sweepBaseIdWithAnExtraMethodThroughAMap(){ fail("""
In file: [###].fear

003| MyId:bb.BaseId[Cu,P]{ #(x) -> x; .extra:P -> P }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "MyId"
Type declaration "MyId" implements "bb.BaseId[_,_]".
Only the method "#(_)" can be declared or inherited here.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
P:{}
Cu:P{}
MyId:bb.BaseId[Cu,P]{ #(x) -> x; .extra:P -> P }
"""); }
  @Test void sweepBaseIdInheritingAMappedImplementation(){ fail("""
In file: [###].fear

001| MyId:bb.BaseId[a.Cu,a.P], a.Forge{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "MyId"
Type declaration "MyId" implements "bb.BaseId[_,_]".
It inherits the implementation of "#(_)" from "a.Forge", which does not implement "bb.BaseId[_,_]".
Method "#(_)" must be implemented here, or inherited from a type implementing "bb.BaseId[_,_]".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "P:{} Cu:{} Forge:{ #(x:Cu):P -> P }"), mapABb, """
MyId:bb.BaseId[a.Cu,a.P], a.Forge{}
"""); }
  @Test void sweepFileLogWithoutFileNameThroughAMap(){ fail("""
In file: [###].fear

001| Foo_bar:bb.FileLog{ .name -> bb.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Foo_bar"
Type declaration "Foo_bar" implements "bb.FileLog", so it writes to a log file named after it.
Type name "Foo_bar" has no file name.
The name of a "bb.FileLog" type can only use letters, digits and underscores, and an underscore cannot be followed by a lowercase letter.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
Foo_bar:bb.FileLog{ .name -> bb.Nope! }
"""); }
  @Test void sweepFileLogFileNameNotAllowedThroughAMap(){ fail("""
In file: [###].fear

001| Con:bb.FileLog{ .name -> bb.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Con"
Type declaration "Con" implements "bb.FileLog", so it writes to the log file ".out/logs/_b/con.log".
"con" is a Windows reserved device name.
Rename "Con", so that its log file has a name allowed in a Fearless project.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
Con:bb.FileLog{ .name -> bb.Nope! }
"""); }
  @Test void sweepMainWithGenericParametersThroughAMap(){ fail("""
In file: [###].fear

001| Hello[X]:bb.Main{ .main -> bb.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Hello[_]"
Type declaration "Hello[_]" implements "bb.Main" and has generic type parameters.
A type implementing "bb.Main" must have zero generic type parameters.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
Hello[X]:bb.Main{ .main -> bb.Void }
"""); }
  @Test void sweepFinalWithoutAMethodNameThroughAMap(){ fail("""
In file: [###].fear

001| A:bb.Final["foo"]{}
   | ^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `bb.Final["foo"]`.
The generic type argument of "bb.Final[_]" is a string literal type holding a method name, like `".name"` or `"+"`.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
A:bb.Final["foo"]{}
"""); }
  @Test void sweepFinalMethodImplementedThroughAMap(){ fail("""
In file: [###].fear

001| Fake:bb.DataRead{ .name -> bb.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Fake"
Type declaration "Fake" implements method ".name".
"bb.Named" implements `bb.Final[".name"]` and type declaration "Fake" implements "bb.Named",
thus type declaration "Fake" cannot override any method named ".name".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
Fake:bb.DataRead{ .name -> bb.Nope! }
"""); }
  @Test void sweepFinalMethodOfAMappedTypeImplemented(){ fail("""
In file: [###].fear

001| B:a.A{ .foo -> this }
   | ^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Type declaration "B" implements method ".foo".
"a.A" implements `base.Final[".foo"]` and type declaration "B" implements "a.A",
thus type declaration "B" cannot override any method named ".foo".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "A:base.Final[\".foo\"]{ .foo:A -> this }"), mapA, """
B:a.A{ .foo -> this }
"""); }
  @Test void sweepOpenWithWithoutMainThroughAMap(){ fail("""
In file: [###].fear

001| Assoc:bb.OpenWith[Icon,"foo"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Assoc"
Type declaration "Assoc" implements "bb.OpenWith[_,_]".
Only a main can implement "bb.OpenWith[_,_]": type declaration "Assoc" must also implement "bb.Main", directly or through one of its supertypes.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
Assoc:bb.OpenWith[Icon,"foo"]{}
Icon:{}
"""); }
  @Test void sweepOpenWithMappedIconNotConcrete(){ fail("""
In file: [###].fear

001| One:bb.Main, bb.OpenWith[a.Box[a.Icon],"foo"]{ .main -> bb.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "One"
Type declaration "One" implements `bb.OpenWith[a.Box[a.Icon],"foo"]`.
"a.Box[a.Icon]" is not a valid icon.
Only concrete types with zero generic type arguments are valid icons.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Box[X]:{} Icon:{}"), mapABb, """
One:bb.Main, bb.OpenWith[a.Box[a.Icon],"foo"]{ .main -> bb.Void }
"""); }
  @Test void sweepOpenWithMappedExtensionNotAString(){ fail("""
In file: [###].fear

001| One:bb.Main, bb.OpenWith[a.Icon,a.Icon]{ .main -> bb.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "One"
Type declaration "One" implements "bb.OpenWith[a.Icon,a.Icon]".
The extension "a.Icon" is not a string literal type.
An extension is written as a string literal type, like `"ffile347"`, `"xml"` or `"txt"`; or implement "bb.OpenWith[_]" to let the Fearless manager choose one.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Icon:{}"), mapABb, """
One:bb.Main, bb.OpenWith[a.Icon,a.Icon]{ .main -> bb.Void }
"""); }
  @Test void sweepOpenWithInvalidExtensionThroughAMap(){ fail("""
In file: [###].fear

001| One:bb.Main, bb.OpenWith[Icon,"Foo"]{ .main -> bb.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "One"
Type declaration "One" implements `bb.OpenWith[Icon,"Foo"]`.
"Foo" is not a valid extension.
An extension is 1 to 16 characters, each a lowercase letter "a"-"z" or a digit "0"-"9", with no dot; or implement "bb.OpenWith[_]" to let the Fearless manager choose one.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
One:bb.Main, bb.OpenWith[Icon,"Foo"]{ .main -> bb.Void }
Icon:{}
"""); }
  @Test void sweepShortcutNotFappThroughAMap(){ fail("""
In file: [###].fear

001| One:bb.Main, bb.Shortcut[Icon,"foo"]{ .main -> bb.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "One"
Type declaration "One" implements `bb.Shortcut[Icon,"foo"]`.
"foo" is not a shortcut extension: a shortcut file only starts its main, so it must not look like a document of another program or a file of the project.
A shortcut extension is "fapp" followed by three digits, like "fapp042"; or implement "bb.Shortcut[_]" to let the Fearless manager choose one.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
One:bb.Main, bb.Shortcut[Icon,"foo"]{ .main -> bb.Void }
Icon:{}
"""); }
  @Test void sweepOpenWithFappThroughAMap(){ fail("""
In file: [###].fear

001| One:bb.Main, bb.OpenWith[Icon,"fapp001"]{ .main -> bb.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "One"
Type declaration "One" implements `bb.OpenWith[Icon,"fapp001"]`.
"fapp001" is a shortcut extension: "fapp" followed by three digits names the shortcut files of the Fearless manager.
Use an extension of the form "ffile" followed by three digits, like "ffile042", or a system extension, like "htm"; or implement "bb.OpenWith[_]" to let the Fearless manager choose one.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
One:bb.Main, bb.OpenWith[Icon,"fapp001"]{ .main -> bb.Void }
Icon:{}
"""); }
  @Test void sweepOpenWithTwiceThroughAMap(){ fail("""
In file: [###].fear

001| Two:bb.Main, bb.OpenWith[Icon,"foo"], bb.OpenWith[Icon2,"foo"]{ .main -> bb.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Two"
Type declaration "Two" claims the extension "foo" more than once:
both `bb.OpenWith[Icon,"foo"]` and `bb.OpenWith[Icon2,"foo"]` claim it.
A main can claim each extension at most once, across all its "bb.OpenWith[_,_]" and "bb.Shortcut[_,_]", since one extension has one icon.

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
Two:bb.Main, bb.OpenWith[Icon,"foo"], bb.OpenWith[Icon2,"foo"]{ .main -> bb.Void }
Icon:{}
Icon2:{}
"""); }
  @Test void sweepLiteralExtendingAnAnonymousLiteralThroughAMap(){ fail("""
In file: [###].fear

002| U:{ .m:bb.Void -> {'s .j:bb.Void -> G#(s, {}) }.j }
   |                                           ^^

While inspecting object literal "{...}" (line 2)
The inference concluded that the object literal at line 2, column 43 should extend the object literal at line 2, column 19;
but an object literal can only extend a standalone type.
A type is standalone if it is declared at top level, or if it implements "bb.CaptureFree".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
G:{ #[X:*](a:X, b:X):bb.Void -> bb.Void }
U:{ .m:bb.Void -> {'s .j:bb.Void -> G#(s, {}) }.j }
"""); }
  @Test void sweepDeadSelfNameInAnInferredLiteralOfAMappedType(){ fail("""
In file: [###].fear

001| Make:{ #:a.A -> {'self} }
   |                 ^^^^^^^

While inspecting object literal instance of "a.A"
The self name "self" is dead code.
No method of the object literal instance of "a.A" uses it.
Remove "'self" from the object literal.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "A:{ read .get:base.Nat -> 0 }"), mapA, """
Make:{ #:a.A -> {'self} }
"""); }
  @Test void sweepIntLiteralOutOfRangeThroughAMap(){ fail("""
In file: [###].fear

001| Main:{ .m:bb.Int -> +421381834238972893748972389723 }
   |                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Integer literal is out of range for "bb.Int".
"bb.Int" must be representable as a 64-bit signed integer.
Valid range: -9223372036854775808 .. 9223372036854775807.
This literal is: "421381834238972893748972389723".
Hint: if you need arbitrary precision numbers, use "bb.Num".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
Main:{ .m:bb.Int -> +421381834238972893748972389723 }
"""); }
  @Test void sweepNatLiteralOutOfRangeThroughAMap(){ fail("""
In file: [###].fear

001| Main:{ .m:bb.Nat -> 421381834238972893748972389723 }
   |                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Natural literal is out of range for "bb.Nat".
"bb.Nat" must be representable as a 64-bit unsigned integer.
Valid range: 0 .. 18446744073709551615.
This literal is: "421381834238972893748972389723".
Hint: if you need arbitrary precision numbers, use "bb.Num".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
Main:{ .m:bb.Nat -> 421381834238972893748972389723 }
"""); }
  @Test void sweepFloatLiteralNotExactlyRepresentableThroughAMap(){ fail("""
In file: [###].fear

001| Main:{ .m:bb.Float -> +0.1 }
   |                       ^^^^

While inspecting the file
Float literal is not exactly representable as "bb.Float".
"bb.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+0.1".
If rounded, the nearest representable value is "+0.1000000000000000055511151231257827021181583404541015625".
Write "+0.1soft" to accept that rounding.
Hint: if you need arbitrary precision numbers, use "bb.Num".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), mapBb, """
Main:{ .m:bb.Float -> +0.1 }
"""); }
  @Test void aMappedNameOnlyInTheCompressedFooterAddsNoNote(){ fail("""
In file: [###].fear

002| B:{ .k: L -> L{'s .m0(x) -> x; .m1(x) -> x; } }
   |     ---------^^------------------------------

While inspecting object literal instance of "L" > ".k" line 2
The self name "s" is dead code.
No method of the object literal instance of "L" uses it.
Remove "'s" from the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
L{'s .m0(x:-.A):-.A->x;.m1(x:-.A):-.A->x}
Error 8 TypeError
""", Map.of("c", "A:{}"), Map.of("a", "c"), """
L:{ .m0(x:a.A):a.A; .m1(x:a.A):a.A; }
B:{ .k: L -> L{'s .m0(x) -> x; .m1(x) -> x; } }
"""); }
  @Test void anAmbiguousTypeArgumentExampleNotesEveryMappedName(){ fail("""
In file: [###].fear

001| U:{ .two[S,T](s:S, x:T, y:T):a.A -> a.A; .use(q:d.Q, y:a.Y, z:a.Z):a.A -> this.two(q, y, z) }
   |                                                                           ^^^^^^^^^^^^^^^^^

While inspecting method call ".two(_,_,_)"
The generic type argument "T" of ".two" is inferred from the arguments, but they disagree: some need "a.Y", some need "a.Z".
"T" could be "a.A" or "a.B2": each is a supertype of "a.Y" and "a.Z". The choice is ambiguous.
Write the generic type argument explicitly, as in "this.two[d.Q,a.A](q, y, z)".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "d" to refer to the code inside folders named "_e", because of "map d as _e in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "A:{} B2:{} Y:A,B2{} Z:A,B2{}", "e", "Q:{}"), Map.of("a", "c", "d", "e"), """
U:{ .two[S,T](s:S, x:T, y:T):a.A -> a.A; .use(q:d.Q, y:a.Y, z:a.Z):a.A -> this.two(q, y, z) }
"""); }
  static final String noteD= "Source code inside folders named \"_b\" uses package name \"d\" to refer to the code inside folders named \"_e\", because of \"map d as _e in _b\", written in fear:/_b/_rank_app.fear.";
  @Test void aMappedAliasOnlyInTheCompressedFooterAddsNoNotes(){ fail("""
In file: [###].fear

003| B:{ .k: L -> L{'s .m0(x) -> x; .m1(x) -> x; } }
   |     ---------^^------------------------------

While inspecting object literal instance of "L" > ".k" line 3
The self name "s" is dead code.
No method of the object literal instance of "L" uses it.
Remove "'s" from the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
L{'s .m0(x:X):X->x;.m1(x:X):X->x}
Error 8 TypeError
""", Map.of("c", "A:{}"), mapA, """
use a.A as X;
L:{ .m0(x:X):X; .m1(x:X):X; }
B:{ .k: L -> L{'s .m0(x) -> x; .m1(x) -> x; } }
"""); }
  @Test void aMappedAliasInTheBodyAndInTheFooterAddsTheAliasNoteAndTheMapNoteOnce(){ fail("""
In file: [###].fear

002| B:{ .k:X -> X{'s .fromC -> this} }
   |     -------------~~~~~~~~~~^^^^^

While inspecting parameter "this" > ".fromC" line 2 > ".k" line 2
Method ".fromC" inside the object literal instance of "iso X" (line 2)
is implemented with an expression returning "B".
Parameter "this" has type "B" instead of a subtype of "X".

Name "X" stands for "a.A" because of "use a.A as X".
"""+noteA+"""


See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
B:{.k:X->X{'s .fromC:X->this}}
Error 8 TypeError
""", Map.of("c", cA), mapA, """
use a.A as X;
B:{ .k:X -> X{'s .fromC -> this} }
"""); }
  @Test void aMappedNameOnlyInTheReasonAndInTheFooterAddsOneNote(){ fail("""
In file: [###].fear

002| B:{ .k:a.A -> L{ .m0(x) -> x; } }
   |     ----------^^---------------

While inspecting object literal instance of "L" > ".k" line 2
The body of method ".k" of type declaration "B" is an expression returning "iso L".
Object literal is of type "iso L" instead of a subtype of "a.A".

"""+noteA+"""


See inferred typing context below for how type "a.A" was introduced: (compression indicated by `-`)
B:{.k:-.A->L{.m0(x:-.A):-.A->x}}
Error 8 TypeError
""", Map.of("c", "A:{}"), mapA, """
L:{ .m0(x:a.A):a.A; }
B:{ .k:a.A -> L{ .m0(x) -> x; } }
"""); }
  @Test void aMappedNameInTheReasonNextToAMappedAliasOnlyInTheFooterAddsOnlyTheMapNote(){ fail("""
In file: [###].fear

003| B:{ .k:a.A2 -> L{ .m0(x) -> x; } }
   |     -----------^^---------------

While inspecting object literal instance of "L" > ".k" line 3
The body of method ".k" of type declaration "B" is an expression returning "iso L".
Object literal is of type "iso L" instead of a subtype of "a.A2".

"""+noteA+"""


See inferred typing context below for how type "a.A2" was introduced: (compression indicated by `-`)
B:{.k:-.A2->L{.m0(x:X):X->x}}
Error 8 TypeError
""", Map.of("c", "A:{} A2:{}"), mapA, """
use a.A as X;
L:{ .m0(x:X):X; }
B:{ .k:a.A2 -> L{ .m0(x) -> x; } }
"""); }
  @Test void aBaseNameThroughAMapInTheBodyAndAMappedNameOnlyInTheFooterNoteOnlyTheBase(){ fail("""
In file: [###].fear

001| B:{ .m(x:a.A):B -> 5 }
   |     ---------------^

While inspecting object literal instance of "bb.Nat" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "iso bb.Nat".
Object literal is of type "bb.Nat" instead of a subtype of "B".

"""+noteBb+"""


See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.A):B->5}
Error 8 TypeError
""", Map.of("c", cA), mapABb, """
B:{ .m(x:a.A):B -> 5 }
"""); }
  @Test void aMappedNameInTheBodyAndABaseNameThroughAMapOnlyInTheFooterNoteOnlyTheMappedName(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A, n:bb.Nat):B->x}
   |    -----------------------^^

While inspecting parameter "x" > ".m(_,_)" line 1
The body of method ".m(_,_)" of type declaration "B" is an expression returning "a.A".
Parameter "x" has type "a.A" instead of a subtype of "B".

"""+noteA+"""


See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.A,n:-.Nat):B->x}
Error 8 TypeError
""", Map.of("c", cA), mapABb, """
B:{.m(x:a.A, n:bb.Nat):B->x}
"""); }
  @Test void twoMappedNamesInTheBodyAndAThirdOnlyInTheFooterGiveTwoNotes(){ fail("""
In file: [###].fear

001| B:{.m(x:z.A, q:d.Q):a.A->x}
   |    ----------------------^^

While inspecting parameter "x" > ".m(_,_)" line 1
The body of method ".m(_,_)" of type declaration "B" is an expression returning "z.A".
Parameter "x" has type "z.A" instead of a subtype of "a.A".

Source code inside folders named "_b" uses package name "z" to refer to the code inside folders named "_c", because of "map z as _c in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_e", because of "map a as _e in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "a.A" was introduced: (compression indicated by `-`)
B:{.m(x:-.A,q:-.Q):-.A->x}
Error 8 TypeError
""", Map.of("c", cA, "e", aA, "f", "Q:{}"), Map.of("z", "c", "a", "e", "d", "f"), """
B:{.m(x:z.A, q:d.Q):a.A->x}
"""); }
  @Test void baseNamesThroughAMapOnlyInTheCompressedFooterAddNoNote(){ fail("""
In file: [###].fear

002| B:{ .k: L -> L{'s .m0(x) -> x; .m1(x) -> x; } }
   |     ---------^^------------------------------

While inspecting object literal instance of "L" > ".k" line 2
The self name "s" is dead code.
No method of the object literal instance of "L" uses it.
Remove "'s" from the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
L{'s .m0(x:-.Nat):-.Nat->x;.m1(x:-.Str):-.Str->x}
Error 8 TypeError
""", Map.of(), mapBb, """
L:{ .m0(x:bb.Nat):bb.Nat; .m1(x:bb.Str):bb.Str; }
B:{ .k: L -> L{'s .m0(x) -> x; .m1(x) -> x; } }
"""); }
  @Test void baseAliasesThroughAMapOnlyInTheCompressedFooterAddNoNotes(){ fail("""
In file: [###].fear

004| B:{ .k: L -> L{'s .m0(x) -> x; .m1(x) -> x; } }
   |     ---------^^------------------------------

While inspecting object literal instance of "L" > ".k" line 4
The self name "s" is dead code.
No method of the object literal instance of "L" uses it.
Remove "'s" from the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
L{'s .m0(x:N):N->x;.m1(x:S):S->x}
Error 8 TypeError
""", Map.of(), mapBb, """
use bb.Nat as N;
use bb.Str as S;
L:{ .m0(x:N):N; .m1(x:S):S; }
B:{ .k: L -> L{'s .m0(x) -> x; .m1(x) -> x; } }
"""); }
  @Test void aBaseNameThroughAMapInTheReasonAndTheFooterAddsOneNote(){ fail("""
In file: [###].fear

002| B:{ .k:bb.Str -> L{ .m0(x) -> x; } }
   |     -------------^^---------------

While inspecting object literal instance of "L" > ".k" line 2
The body of method ".k" of type declaration "B" is an expression returning "iso L".
Object literal is of type "iso L" instead of a subtype of "bb.Str".

"""+noteBb+"""


See inferred typing context below for how type "bb.Str" was introduced: (compression indicated by `-`)
B:{.k:-.Str->L{.m0(x:-.Nat):-.Nat->x}}
Error 8 TypeError
""", Map.of(), mapBb, """
L:{ .m0(x:bb.Nat):bb.Nat; }
B:{ .k:bb.Str -> L{ .m0(x) -> x; } }
"""); }
  @Test void mappedTypeArgumentsOnlyInTheCompressedFooterAddNoNote(){ fail("""
In file: [###].fear

002| B:{ .k: L -> L{'s .m0(x) -> x; .m1(x) -> x; } }
   |     ---------^^------------------------------

While inspecting object literal instance of "L" > ".k" line 2
The self name "s" is dead code.
No method of the object literal instance of "L" uses it.
Remove "'s" from the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
L{'s .m0(x:-.Box[-.Q]):-.Box[-.Q]->x;.m1(x:-.Box[-.Q]):-.Box[-.Q]->x}
Error 8 TypeError
""", Map.of("c", "Box[T]:{}", "e", "Q:{}"), Map.of("a", "c", "d", "e"), """
L:{ .m0(x:a.Box[d.Q]):a.Box[d.Q]; .m1(x:a.Box[d.Q]):a.Box[d.Q]; }
B:{ .k: L -> L{'s .m0(x) -> x; .m1(x) -> x; } }
"""); }
  @Test void aMappedGenericTypeOnlyInTheFrameNotesItsPackageButNotItsUnprintedTypeArgument(){ fail("""
In file: [###].fear

001| B:{ .m:a.Box[d.Q] -> { .k -> B; }; }
   |                      --^^^^^^^---

While inspecting object literal instance of "a.Box[_]"
Missing return type for method ".k".
Add an explicit return type before '->'.
Alternatively (less common), if you intended to override and omit the signature,
the signature must be inherited from a supertype.
Cannot infer signature of method ".k".
No supertype has a method named ".k" with 0 parameters.

"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", "Box[T]:{}", "e", "Q:{}"), Map.of("a", "c", "d", "e"), """
B:{ .m:a.Box[d.Q] -> { .k -> B; }; }
"""); }
  static final String cI12= "I1:{ .m:base.Void -> base.Void } I2:{ .m:base.Void -> base.Void }";
  @Test void anAliasAndAQualifiedNameThroughOneMapInAWellFormednessErrorGiveOneMapNote(){ fail("""
In file: [###].fear

002| B:X,a.I2{}
   | ^^^^^^^^^^

While inspecting type declaration "B"
Ambiguous implementation for method ".m" with 0 parameters.
Different options are present in the implemented types.
Candidates: "X", "a.I2".
Type declaration "B" must declare a method ".m" explicitly implementing the desired behaviour.

Name "X" stands for "a.I1" because of "use a.I1 as X".
"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", cI12), mapA, """
use a.I1 as X;
B:X,a.I2{}
"""); }
  @Test void twoMapsInAWellFormednessErrorGiveTwoNotesInTheOrderTheNamesArePrinted(){ fail("""
In file: [###].fear

001| B:d.I2,a.I1{}
   | ^^^^^^^^^^^^^

While inspecting type declaration "B"
Ambiguous implementation for method ".m" with 0 parameters.
Different options are present in the implemented types.
Candidates: "d.I2", "a.I1".
Type declaration "B" must declare a method ".m" explicitly implementing the desired behaviour.

"""+noteD+"\n"+noteA+"""

Error 7 WellFormedness
""", Map.of("c", "I1:{ .m:base.Void -> base.Void }", "e", "I2:{ .m:base.Void -> base.Void }"), Map.of("a", "c", "d", "e"), """
B:d.I2,a.I1{}
"""); }
  @Test void aMappedSupertypeNotPrintedInAWellFormednessErrorAddsNoNote(){ fail("""
In file: [###].fear

001| B:a.A{ .k:B -> this; .k:B -> this; }
   | -----~~~~~~~~~~~~~~~~^^^^^^^^^^^^~~~

While inspecting type declaration body > type declaration > full file
Method ".k" with 0 parameters redeclared.
A method with the same name, arity and reference capability is already present.
Error 7 WellFormedness
""", Map.of("c", cA), mapA, """
B:a.A{ .k:B -> this; .k:B -> this; }
"""); }
  @Test void aMappedAliasNotPrintedInAParserErrorAddsNoNote(){ fail("""
In file: [###].fear

001| use a.A as X;
002| B:{ .m(x:X, x:X):B -> this }
   |   --^^^^^^^^^^^^^^~~~~~~~~--

While inspecting method signature > method declaration > type declaration body > type declaration > full file
A method signature cannot declare multiple parameters with the same name.
Parameter "x" is repeated.
Error 2 UnexpectedToken
""", Map.of("c", cA), mapA, """
use a.A as X;
B:{ .m(x:X, x:X):B -> this }
"""); }
  @Test void anAliasOfABaseTypeAndAHintThroughTheSameMapGiveOneMapNote(){ fail("""
In file: [###].fear

002| Main:{ .m:I -> +421381834238972893748972389723 }
   |                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Integer literal is out of range for "I".
"I" must be representable as a 64-bit signed integer.
Valid range: -9223372036854775808 .. 9223372036854775807.
This literal is: "421381834238972893748972389723".
Hint: if you need arbitrary precision numbers, use "bb.Num".

Name "I" stands for "bb.Int" because of "use bb.Int as I".
"""+noteBb+"""

Error 7 WellFormedness
""", Map.of(), mapBb, """
use bb.Int as I;
Main:{ .m:I -> +421381834238972893748972389723 }
"""); }
}