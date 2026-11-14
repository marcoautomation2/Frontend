package typeSystem;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

import core.AllLs;
import core.FearlessException;
import main.FrontendLogicMain;
import testUtils.DbgBlock;

public final class TypeInMethodTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }

  static void okTwoPkgs(String aSrc, String bSrc){
    var oB= oraclePkg(List.of(bSrc));
    var res= okOrPrint(oB, () -> compileB(aSrc, oB));
    if (!checkCompact){ return; }
    coreCmp(lines(res), compact.Print.lines(compactB(aSrc, oB)));
  }
  static void failTwoPkgs(String expected, String aSrc, String bSrc){
    failTwoPkgsRaw("In file: [###].fear\n\n"+expected+"Error 8 TypeError", aSrc, bSrc);
  }
  static void failTwoPkgsRaw(String expected, String aSrc, String bSrc){
    var oB= oraclePkg(List.of(bSrc));
    var fe= assertThrows(FearlessException.class, () -> compileB(aSrc, oB));
    strCmp(expected, fe.render(oB));
    if (!checkCompact){ return; }
    assertThrows(compact.Frontend.Fail.class, () -> compactB(aSrc, oB));
  }
  private static List<compact.Frontend.Literal> compactB(String aSrc, tools.SourceOracle oB){
    var base= compactBase();
    var aLits= compactAll("a", oraclePkg(List.of(aSrc)), base).stream().flatMap(TypeInMethodTest::compactAllLs);
    return compactAll("b", oB, Stream.concat(base.stream(), aLits).toList());
  }
  private static List<core.E.Literal> compileB(String aSrc, tools.SourceOracle oB){
    var base= otherFrom(DbgBlock.all());
    var oA= oraclePkg(List.of(aSrc));
    var aLits= okOrPrint(oA, () -> compileAll("a", oA, base));
    var other= base.mergeWith(AllLs.of(aLits), -1);
    return new FrontendLogicMain().of("b", Map.of(), oB.allFiles(), other);
  }
  private static final String byName= """
002| B:{.m:A->A}
   |    ------^^

While inspecting object literal instance of "A" > ".m" line 2
The type "A" is not standalone: it is declared inside a method body.
Only a standalone type can be extended or mentioned by name.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
A
""";
  private static final String byNameOtherPkg= """
001| B:{.m:a.A->a.A}
   |    --------^^^^

While inspecting object literal instance of "a.A" > ".m" line 1
The type "a.A" is not standalone: it is declared inside a method body.
Only a standalone type can be extended or mentioned by name.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
-.A
""";

  @Test void topLevelTypeByName(){ ok(List.of("""
A:{}
B:{.m:A->A}
""")); }

  @Test void captureFreeTypeInMethodByName(){ ok(List.of("""
A0:{.m:A->A:base.CaptureFree{}}
B:{.m:A->A}
""")); }

  @Test void typeInMethodNeverInstantiated(){ ok(List.of("""
A0:{.m(x:A0):A->A:{.foo:A0->x}}
""")); }

  @Test void typeInMethodCapturingThisByName(){ fail(byName, List.of("""
A0:{.m:A->A:{.foo:A0->this}}
B:{.m:A->A}
""")); }

  @Test void typeInMethodCapturingParameterByName(){ fail(byName, List.of("""
A0:{.m(x:A0):A->A:{.foo:A0->x}}
B:{.m:A->A}
""")); }

  @Test void typeInMethodCapturingNothingByName(){ fail(byName, List.of("""
A0:{.m:A->A:{}}
B:{.m:A->A}
""")); }

  @Test void typeInMethodCapturingNothingByNameUseAlias(){ fail("""
003| B:{.m:A->A}
   |    ------^^

While inspecting object literal instance of "A" > ".m" line 3
The type "A" is not standalone: it is declared inside a method body.
Only a standalone type can be extended or mentioned by name.
A type is standalone if it is declared at top level, or if it implements "CF".

Compressed relevant code with inferred types: (compression indicated by `-`)
A
""", List.of("""
use base.CaptureFree as CF;
A0:{.m:A->A:{}}
B:{.m:A->A}
""")); }

  @Test void typeInMethodExtended(){ fail("""
002| B:A{}
   | ^^^^^

While inspecting type declaration "B"
The type "A" is not standalone: it is declared inside a method body.
Only a standalone type can be extended or mentioned by name.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
B:A{}
""", List.of("""
A0:{.m(x:A0):A->A:{.foo:A0->x}}
B:A{}
""")); }

  @Test void captureFreeTypeInMethodExtended(){ ok(List.of("""
A0:{.m:A->A:base.CaptureFree{}}
B:A{}
""")); }

  @Test void captureFreeTypeInMethodWithSelfNameMutMethodCalledByName(){ ok(List.of("""
Foo:{}
A0:{.m:A->A:base.CaptureFree{'self mut .x:Foo->Foo; read .me:imm A->self}}
B:{.m:mut A->mut A; .u:Foo->this.m.x[mut]}
""")); }

  @Test void captureFreeTypeInMethodWithoutSelfNameMutMethodCalledByName(){ ok(List.of("""
Foo:{}
A0:{.m:A->A:base.CaptureFree{mut .x:Foo->Foo}}
B:{.m:mut A->mut A; .u:Foo->this.m.x[mut]}
""")); }

  @Test void captureFreeTypeInMethodWithAbstractMutMethodMutMethodCalledOnSubtype(){ ok(List.of("""
Foo:{}
Y:{mut .y:Foo}
A0:{.m:A->A:base.CaptureFree,Y{mut .x:Foo->Foo}}
B:A{mut .y:Foo->Foo}
C:{.m:mut B->mut B; .u:Foo->this.m.x[mut]}
""")); }

  @Test void anonReceiverTypeInMethodHead(){ ok(List.of("""
A0:{.m(x:A0):A->A:{.foo:A0->x}}
B:{.m(a:A):A->{ .get: A -> a }.get}
""")); }

  @Test void anonReceiverCaptureFreeTypeInMethodHead(){ ok(List.of("""
A0:{.m:A->A:base.CaptureFree{ .get(x:A): A -> x }}
B:{.m(a:A):A->{ .get(x) -> x }.get(a)}
""")); }

  @Test void anonReceiverPrivateHeadFromOtherPkg(){ okTwoPkgs("""
_P:{ .foo: base.Void }
Q:_P{ .foo -> base.Void }
Take:{ #(p:_P): base.Void -> base.Void }
""", """
B:{.m: base.Void -> a.Take#({ .q: a.Q -> a.Q }.q)}
"""); }

  @Test void anonArgumentImplementsPrivateTypeFromOtherPkg(){ failTwoPkgsRaw("""
In file: [###].fear

001| B:{.m: base.Void -> a.Take#({ base.Void })}
   |                             ^^^^^^^^^^^^^

While inspecting object literal instance of "a._P"
Object literal instance of "a._P" implements private type "a._P".
Private types can only be implemented in their own package.
Object literal instance of "a._P" is in package "b".
Type "a._P" is in package "a".
Error 7 WellFormedness""", """
_P:{ .foo: base.Void }
Take:{ #(p:_P): base.Void -> base.Void }
""", """
B:{.m: base.Void -> a.Take#({ base.Void })}
"""); }

  @Test void anonEmptyArgumentImplementsPrivateTypeFromOtherPkg(){ failTwoPkgsRaw("""
In file: [###].fear

001| B:{.m: base.Void -> a.Take#({})}
   |                             ^^

While inspecting object literal instance of "a._P"
Object literal instance of "a._P" implements private type "a._P".
Private types can only be implemented in their own package.
Object literal instance of "a._P" is in package "b".
Type "a._P" is in package "a".
Error 7 WellFormedness""", """
_P:{ .foo: base.Void -> base.Void }
Take:{ #(p:_P): base.Void -> base.Void }
""", """
B:{.m: base.Void -> a.Take#({})}
"""); }

  @Test void anonEmptyArgumentImplementsAbstractPrivateTypeFromOtherPkg(){ failTwoPkgsRaw("""
In file: [###].fear

001| B:{.m: base.Void -> a.Take#({})}
   |                             ^^

While inspecting object literal instance of "a._P"
Object literal instance of "a._P" implements private type "a._P".
Private types can only be implemented in their own package.
Object literal instance of "a._P" is in package "b".
Type "a._P" is in package "a".
Error 7 WellFormedness""", """
_P:{ .foo: base.Void }
Take:{ #(p:_P): base.Void -> base.Void }
""", """
B:{.m: base.Void -> a.Take#({})}
"""); }

  @Test void typedLiteralImplementsPrivateTypeFromOtherPkg(){ failTwoPkgsRaw("""
In file: [###].fear

001| B:{.m: base.Void -> a.Take#(a._P{ base.Void })}
   |                     --------^^^^~~~~~~~~~~~~~-

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Code is attempting to use private name "_P" from package "a".
Type names starting with "_" can only be used in their own package, and only by their simple name.
Error 2 UnexpectedToken""", """
_P:{ .foo: base.Void }
Take:{ #(p:_P): base.Void -> base.Void }
""", """
B:{.m: base.Void -> a.Take#(a._P{ base.Void })}
"""); }

  @Test void anonArgumentImplementsSealedTypeFromOtherPkg(){ failTwoPkgsRaw("""
In file: [###].fear

001| B:{.m: base.Void -> a.Take#({ base.Void })}
   |                             ^^^^^^^^^^^^^

While inspecting object literal instance of "a.S"
Object literal instance of "a.S" implements sealed type "a.S".
Sealed types can only be implemented in their own package.
Object literal instance of "a.S" is in package "b".
Type "a.S" is in package "a".
Error 7 WellFormedness""", """
S:base.Sealed{ .foo: base.Void }
Take:{ #(p:S): base.Void -> base.Void }
""", """
B:{.m: base.Void -> a.Take#({ base.Void })}
"""); }

  @Test void anonEmptyArgumentOfAbstractSealedTypeFromOtherPkg(){ failTwoPkgsRaw("""
In file: [###].fear

001| B:{.m: base.Void -> a.Take#({})}
   |    -------------------------^^-

While inspecting object literal instance of "iso a.S" > ".m" line 1
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "a.S".
Sealed types can only be implemented in their own package.
Type "a.S" is in package "a".

Compressed relevant code with inferred types: (compression indicated by `-`)
iso -.S
Error 8 TypeError""", """
S:base.Sealed{ .foo: base.Void }
Take:{ #(p:S): base.Void -> base.Void }
""", """
B:{.m: base.Void -> a.Take#({})}
"""); }

  @Test void typeExpressionOfAbstractSealedTypeFromOtherPkg(){ failTwoPkgsRaw("""
In file: [###].fear

001| B:{.m: base.Void -> a.Take#(a.S)}
   |    -------------------------^^^^

While inspecting object literal instance of "iso a.S" > ".m" line 1
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "a.S".
Sealed types can only be implemented in their own package.
Type "a.S" is in package "a".

Compressed relevant code with inferred types: (compression indicated by `-`)
iso -.S
Error 8 TypeError""", """
S:base.Sealed{ .foo: base.Void }
Take:{ #(p:S): base.Void -> base.Void }
""", """
B:{.m: base.Void -> a.Take#(a.S)}
"""); }

  @Test void anonReceiverTypeInMethodHeadFromOtherPkg(){ okTwoPkgs("""
A0:{.m(x:A0):A->A:{.foo:A0->x}}
""", """
B:{.m(a:a.A):a.A->{ .get: a.A -> a }.get}
"""); }

  @Test void topLevelTypeByNameFromOtherPkg(){ okTwoPkgs("""
A:{}
""", """
B:{.m:a.A->a.A}
"""); }

  @Test void captureFreeTypeInMethodByNameFromOtherPkg(){ okTwoPkgs("""
A0:{.m:A->A:base.CaptureFree{}}
""", """
B:{.m:a.A->a.A}
"""); }

  @Test void typeInMethodCapturingThisByNameFromOtherPkg(){ failTwoPkgs(byNameOtherPkg, """
A0:{.m:A->A:{.foo:A0->this}}
""", """
B:{.m:a.A->a.A}
"""); }

  @Test void typeInMethodCapturingParameterByNameFromOtherPkg(){ failTwoPkgs(byNameOtherPkg, """
A0:{.m(x:A0):A->A:{.foo:A0->x}}
""", """
B:{.m:a.A->a.A}
"""); }

  @Test void typeInMethodExtendedFromOtherPkg(){ failTwoPkgs("""
001| B:a.A{}
   | ^^^^^^^

While inspecting type declaration "B"
The type "a.A" is not standalone: it is declared inside a method body.
Only a standalone type can be extended or mentioned by name.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
B:-.A{}
""", """
A0:{.m(x:A0):A->A:{.foo:A0->x}}
""", """
B:a.A{}
"""); }

  @Test void anonEmptyArgumentRefinedToPrivateTypeFromOtherPkg(){ failTwoPkgsRaw("""
In file: [###].fear

001| B:{.m: a.Sup -> a.Ids#({}, a.Get.p)}
   |                        ^^

While inspecting object literal instance of "a._P"
Object literal instance of "a._P" implements private type "a._P".
Private types can only be implemented in their own package.
Object literal instance of "a._P" is in package "b".
Type "a._P" is in package "a".
Error 7 WellFormedness""", """
Sup:{}
_P:Sup{}
Box[X]:{ .get: X }
Ids:{ #[X](a: X, b: Box[X]): X -> a }
Get:{ .p: Box[_P] -> { _P } }
""", """
B:{.m: a.Sup -> a.Ids#({}, a.Get.p)}
"""); }
}
