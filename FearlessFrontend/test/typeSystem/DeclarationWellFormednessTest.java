package typeSystem;

import java.net.URI;
import java.util.List;

import org.junit.jupiter.api.Test;

import tools.SourceOracle;

public final class DeclarationWellFormednessTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }
  static void failWf(String expected, List<String> input){
    typeFailRaw("In file: [###].fear\n\n"+expected+"Error 7 WellFormedness", input);
  }
  static void failParse(String expected, List<String> input){
    typeFailRaw("In file: [###].fear\n\n"+expected+"Error 2 UnexpectedToken", input);
  }

@Test void unclosedLiteralAtEndOfFile(){typeFailRaw("""
In file: [###].fear

001| X:{
   |   ^

While inspecting groups of parenthesis
File ended while parsing a "{" group.
This "{" may be unintended.
Otherwise expected one of: "}id", "}".
Error 0 Unclosed""", List.of("X:{"));}
@Test void noExplicitThisSelfName(){failParse("""
001| A:{ .m1: A -> {'this} }
   |     ----------~~^^^^~

While inspecting object literal > method body > method declaration > type declaration body > type declaration > full file
Name "this" is already in scope.
""", List.of("""
A:{ .m1: A -> {'this} }
"""));}
@Test void noExplicitThisMethArg(){failParse("""
001| A:{ .foo(this: A): A }
   |     -----^^^^~~~----

While inspecting method parameters declaration > method declaration > type declaration body > type declaration > full file
Name "this" is already in scope.
""", List.of("""
A:{ .foo(this: A): A }
"""));}
@Test void disjointArgList(){failParse("""
001| A:{ .foo(a: A, a: A): A }
   | --~~^^^^^^^^^^^^^^^^^^^~~

While inspecting method declaration > type declaration body > type declaration > full file
A method signature cannot declare multiple parameters with the same name.
Parameter "a" is repeated.
""", List.of("""
A:{ .foo(a: A, a: A): A }
"""));}
@Test void disjointMethGens(){failParse("""
001| A:{ .foo[T:*,T:*](a: T, b: T): A }
   | --~~^^^^^^^^^^^^^^^^^^^^^^^^^^^^~~

While inspecting method declaration > type declaration body > type declaration > full file
A method signature cannot declare multiple generic type parameters with the same name.
Generic type parameter "T" is repeated.
""", List.of("""
A:{ .foo[T:*,T:*](a: T, b: T): A }
"""));}
@Test void disjointDecGens(){failParse("""
001| A[T:*,T:*]:{ .foo(a: T, b: T): A }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration > full file
A type declaration cannot declare multiple generic type parameters with the same name.
Generic type parameter "T" is repeated.
""", List.of("""
A[T:*,T:*]:{ .foo(a: T, b: T): A }
"""));}
@Test void noShadowingMeths(){failWf("""
001| A:{ .a: A; .a: A }
   | --~~~~~~~~~^^^^^~~

While inspecting type declaration body > type declaration > full file
Method ".a" with 0 parameters redeclared.
A method with the same name, arity and reference capability is already present.
""", List.of("""
A:{ .a: A; .a: A }
"""));}
@Test void useUndefinedX(){failParse("""
001| A[X:*]:{ .foo(x: X): X -> B{ x }.argh }
002| B:{ read .argh: read/imm X }
   |   --~~~~~~~~~~~~~~~~~~~~~^--

While inspecting method declaration > type declaration body > type declaration > full file
Generic type parameter "X" is not in scope.
No generic type parameters are declared here.
""", List.of("""
A[X:*]:{ .foo(x: X): X -> B{ x }.argh }
B:{ read .argh: read/imm X }
"""));}
@Test void useUndefinedIdent(){failParse("""
001| A[X:*]:{ .foo(x: X): X -> this.foo(b) }
   |          -----------------~~~~~~~~~^~

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Name "b" is not in scope.
In scope: "this", "x".
""", List.of("""
A[X:*]:{ .foo(x: X): X -> this.foo(b) }
"""));}
@Test void noShadowingSelfName(){failParse("""
001| Foo:{ .m1: Foo -> Foo{ 'unique
002|   .m1 -> {'unique}
   |   -------~~^^^^^^~
003|   } }

While inspecting object literal > method body > method declaration > typed literal > method body > method declaration > type declaration body > type declaration > full file
Name "unique" is already in scope.
""", List.of("""
Foo:{ .m1: Foo -> Foo{ 'unique
  .m1 -> {'unique}
  } }
"""));}
@Test void noTopLevelSelfName(){failWf("""
001| A:{ 'self
   |      ^^^^
002|   .me: A -> self;
003|   }

While inspecting type declaration body > type declaration > full file
Self name "self" is invalid in a top level type.
The self name of a top level type can only be "this".
""", List.of("""
A:{ 'self
  .me: A -> self;
  }
"""));}
@Test void lambdaSelfNameOk(){ok(List.of("""
A:{ .me: A -> {'self .me -> self} }
"""));}
@Test void selfNameDeadCodeLiteralWithoutMethods(){failWf("""
002| Make:{ #: A -> A{'self} }
   |[###]

While inspecting object literal instance of "A"
The self name "self" is dead code.
No method of the object literal instance of "A" uses it.
Remove "'self" from the object literal.
""", List.of("""
A:{ read .get: base.Nat -> 0 }
Make:{ #: A -> A{'self} }
"""));}
@Test void selfNameDeadCodeInferredLiteralWithoutMethods(){failWf("""
002| Make:{ #: A -> {'self} }
   |[###]

While inspecting object literal instance of "A"
The self name "self" is dead code.
No method of the object literal instance of "A" uses it.
Remove "'self" from the object literal.
""", List.of("""
A:{ read .get: base.Nat -> 0 }
Make:{ #: A -> {'self} }
"""));}
@Test void noShadowingOk(){ok(List.of("""
A:{ .m1(a: A): A -> {.m1(b) -> a} }
"""));}
@Test void noShadowingParam(){failParse("""
001| A:{ .m1(a: A): A -> {.m1(a) -> a} }
   |                      ~~~~^~-----

While inspecting method parameters declaration > method signature > method declaration > object literal > method body > method declaration > type declaration body > type declaration > full file
Name "a" is already in scope.
""", List.of("""
A:{ .m1(a: A): A -> {.m1(a) -> a} }
"""));}
@Test void lambdaImplementingItself(){failWf("""
001| A:A{}
   |   ^^

While inspecting type declarations
Circular implementation relation found involving "A".
""", List.of("""
A:A{}
"""));}
@Test void noMutHLambdaCreation(){failParse("""
001| A:{ #: mutH A -> mutH A }
   |     -------------^^^^~~

While inspecting method body > method declaration > type declaration body > type declaration > full file
Capability mutH used.
Capabilities readH and mutH are not allowed on object literals.
Use one of read, mut, imm, iso.
""", List.of("""
A:{ #: mutH A -> mutH A }
"""));}
@Test void noReadHLambdaCreation(){failParse("""
001| A:{ #: readH A -> readH A }
   |     --------------^^^^^~~

While inspecting method body > method declaration > type declaration body > type declaration > full file
Capability readH used.
Capabilities readH and mutH are not allowed on object literals.
Use one of read, mut, imm, iso.
""", List.of("""
A:{ #: readH A -> readH A }
"""));}
@Test void noReadImmLambdaCreation(){failParse("""
001| A:{ #: A -> this.eat(read/imm A); .eat(a: A): A -> a }
   |             ---------^^^^^^^^~~-

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Missing expression.
Found instead: "read/imm".
Expected one of: "name", "type name", "(", "{".
""", List.of("""
A:{ #: A -> this.eat(read/imm A); .eat(a: A): A -> a }
"""));}
@Test void noReadImmOnNominalType(){failParse("""
001| A:{ #: read/imm A -> this# }
   |     ~~~~~~~~~~~~^---------

While inspecting method signature > method declaration > type declaration body > type declaration > full file
Generic type parameter "A" is not in scope.
No generic type parameters are declared here.
""", List.of("""
A:{ #: read/imm A -> this# }
"""));}
@Test void abstractMethodOnlyAtTopLevel(){failWf("""
001| A:{ .foo: A }
002| B:A{}
003| Bs:{ #: B -> B{ .foo: A } }
   |              -~~^^^^^^^~~

While inspecting method declaration > typed literal > method body > method declaration > type declaration body > type declaration > full file
Abstract method declaration for ".foo" with 0 parameters.
Only top level methods can be abstract.
""", List.of("""
A:{ .foo: A }
B:A{}
Bs:{ #: B -> B{ .foo: A } }
"""));}
@Test void validPosInt(){ok(List.of("""
A:{ #: base.Int -> +5 }
"""));}
@Test void validNegInt(){ok(List.of("""
A:{ #: base.Int -> -5 }
"""));}
@Test void validNat(){ok(List.of("""
A:{ #: base.Nat -> 5 }
"""));}
@Test void validFloat(){ok(List.of("""
A:{ #: base.Float -> +5.5 }
"""));}
@Test void validString(){ok(List.of("""
A:{ #: base.Str -> "Hello" }
"""));}
@Test void duplicatedDeclarationTopLevelAndInline(){failWf("""
002| B:{ #: A -> A:{} }
   |             ^^

While inspecting a type name
Duplicate type declaration for "A".
""", List.of("""
A:{}
B:{ #: A -> A:{} }
"""));}
@Test void duplicatedInlineDeclarations(){failWf("""
002| C:{ #: A -> A:{} }
   |             ^^

While inspecting a type name
Duplicate type declaration for "A".
""", List.of("""
B:{ #: A -> A:{} }
C:{ #: A -> A:{} }
"""));}
@Test void inlineDeclarationCalledTwice(){ok(List.of("""
B:{ #: A -> A:{} }
C1:{ #: A -> B# }
C2:{ #: A -> B# }
"""));}
@Test void inlineDeclarationResultUsedTwice(){ok(List.of("""
B:{ #: A -> A:{} }
C1:{ #(b: B): A -> C2#(b#, b#) }
C2:{ #(a1: A, a2: A): A -> a1 }
"""));}
@Test void allowTopLevelDeclInsideMethod(){ok(List.of("""
Str:{} Bob:Str{}
Nat:{} TwentyFour:Nat{}
FPerson:{ #(name: Str, age: Nat): Person -> Person:{
  .name: Str -> name;
  .age: Nat -> age;
  }}
Ex:{
  .create: Person -> FPerson#(Bob, TwentyFour);
  .name(p: Person): Str -> p.name;
  }
"""));}
@Test void cannotImplementDeclarationDeclaredInsideMethod(){fail("""
006| Bad:Person{}
   | ^^^^^^^^^^^^

While inspecting type declaration "Bad"
The type "Person" is not standalone: it is declared inside a method body.
Only a standalone type can be extended or mentioned by name.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
Bad:Person{}
""", List.of("""
Str:{} Nat:{}
FPerson:{ #(name: Str, age: Nat): Person -> Person:{
  .name: Str -> name;
  .age: Nat -> age;
  }}
Bad:Person{}
"""));}
@Test void noFreeGensInInlineDeclaration(){failParse("""
002| FPerson:{ #[N:*](name: Str, age: N): Person -> Person:{
003|   .name: Str -> name;
004|   .age: N -> age;
   |   ~~~~~~^-------
005|   }}

While inspecting method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Generic type parameter "N" is not in scope inside the type declaration "Person".
A type declaration only sees the generic type parameters it declares itself; here "Person" declares none.
Hint: funnel "N" into "Person" by writing "Person[N:..]", restating the bounds of "N".
""", List.of("""
Str:{}
FPerson:{ #[N:*](name: Str, age: N): Person -> Person:{
  .name: Str -> name;
  .age: N -> age;
  }}
"""));}
@Test void genericFunnelling(){ok(List.of("""
Str:{}
FPerson:{ #[N:imm](name: Str, age: N): Person[N] -> Person[N:imm]:{
  .name: Str -> name;
  .age: N -> age;
  }}
"""));}
@Test void genericFunnellingFresh(){ok(List.of("""
Str:{}
Person[N:imm]:{ .name: Str; .age: N }
FPerson:{ #[N:imm](name: Str, age: N): Person[N] -> {
  .name -> name;
  .age -> age;
  }}
"""));}
@Test void genericFunnellingFreshNoBody(){ok(List.of("""
Str:{}
Person[N:imm]:{ .name: Str; .age: N }
Person2[N:imm]:Person[N]{ .name -> this.name; .age -> this.age }
FPerson:{ #[N:imm](name: Str, age: N): Person[N] -> Person2[N] }
"""));}
@Test void nonExistentImplInline(){failWf("""
002| BreakOuter:{ #: BreakInner -> BreakInner: A[imm Break]{} }
   |                                                 ^^^^^^

While inspecting a type name
Type "Break" is not declared in package "p" and is not made visible via "use".
In scope: "A", "BreakInner", "BreakOuter".
""", List.of("""
A[X:mut]:{}
BreakOuter:{ #: BreakInner -> BreakInner: A[imm Break]{} }
"""));}
@Test void inlineDeclarationImplementingAnEnclosingGenericWithoutFunnelling(){failParse("""
001| A[X:mut]:{}
002| BreakOuter[Z:mut]:{ #: BreakInner -> BreakInner: A[Z]{} }
   |                                      ------------~~^~--

While inspecting generic type arguments > super types declaration > method body > method declaration > type declaration body > type declaration > full file
Generic type parameter "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic type parameters it declares itself; here "BreakInner" declares none.
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Z:..]", restating the bounds of "Z".
""", List.of("""
A[X:mut]:{}
BreakOuter[Z:mut]:{ #: BreakInner -> BreakInner: A[Z]{} }
"""));}
@Test void inlineDeclarationImplementingAnEnclosingGenericWithFunnelling(){ok(List.of("""
A[X:mut]:{}
BreakOuter[Z:mut]:{ #: BreakInner[Z] -> BreakInner[Z:mut]: A[Z]{} }
"""));}
@Test void inlineDeclarationUsingAnEnclosingGenericWithoutFunnelling(){failParse("""
001| A[X:*]:{}
002| BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z: A[Z] -> A[Z] } }
   |                                                 ~~~~~~^~--------

While inspecting generic type arguments > method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Generic type parameter "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic type parameters it declares itself; here "BreakInner" declares none.
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Z:..]", restating the bounds of "Z".
""", List.of("""
A[X:*]:{}
BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z: A[Z] -> A[Z] } }
"""));}
@Test void inlineDeclarationUsingAnEnclosingGenericWithFunnelling(){ok(List.of("""
A[X:*]:{}
BreakOuter[Z:*]:{ #: BreakInner[Z] -> BreakInner[Z:*]:{ .z: A[Z] -> A[Z] } }
"""));}
@Test void inlineDeclarationUsingAnEnclosingGenericWithCapabilityWithoutFunnelling(){failParse("""
001| A[X:mut]:{}
002| BreakOuter[Z:mut]:{ #: BreakInner -> BreakInner: A[mut Z]{} }
   |                                                  --~~~~^-

While inspecting generic type arguments > super types declaration > method body > method declaration > type declaration body > type declaration > full file
Generic type parameter "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic type parameters it declares itself; here "BreakInner" declares none.
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Z:..]", restating the bounds of "Z".
""", List.of("""
A[X:mut]:{}
BreakOuter[Z:mut]:{ #: BreakInner -> BreakInner: A[mut Z]{} }
"""));}
@Test void inlineDeclarationPartiallyFunnelled(){failParse("""
001| A[X:*]:{}
002| BreakOuter[Y:*,Z:*]:{ #: BreakInner[Y] -> BreakInner[Y:*]:{ .z: A[Z] -> A[Z] } }
   |                                                             ~~~~~~^~--------

While inspecting generic type arguments > method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Generic type parameter "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic type parameters it declares itself; here "BreakInner" declares "Y".
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Y:..,Z:..]", restating the bounds of "Z".
""", List.of("""
A[X:*]:{}
BreakOuter[Y:*,Z:*]:{ #: BreakInner[Y] -> BreakInner[Y:*]:{ .z: A[Z] -> A[Z] } }
"""));}
@Test void inlineDeclarationCannotRedeclareAHiddenGeneric(){failParse("""
001| A[X:*]:{}
002| BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z[Z:*](z: Z): Z -> z } }
   |                                                 ---^~~----------

While inspecting generic bounds declaration > method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Name "Z" is already in scope.
""", List.of("""
A[X:*]:{}
BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z[Z:*](z: Z): Z -> z } }
"""));}
@Test void inlineDeclarationInsideInlineDeclarationCannotFunnelAHiddenGeneric(){failParse("""
001| A:{}
002| BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z: A -> Inner2[Z:*]: A{} } }
   |                                                          -------^~~------

While inspecting generic bounds declaration > method body > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Generic type parameter "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic type parameters it declares itself; here "BreakInner" declares none.
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Z:..]", restating the bounds of "Z".
""", List.of("""
A:{}
BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z: A -> Inner2[Z:*]: A{} } }
"""));}
@Test void inlineDeclarationUsingAnEnclosingGenericAsReadImmWithoutFunnelling(){failParse("""
001| A:{}
002| BreakOuter[Z:*]:{ #(z: Z): BreakInner -> BreakInner:{ .z: read/imm Z -> z } }
   |                                                       ~~~~~~~~~~~~~^-----

While inspecting method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Generic type parameter "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic type parameters it declares itself; here "BreakInner" declares none.
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Z:..]", restating the bounds of "Z".
""", List.of("""
A:{}
BreakOuter[Z:*]:{ #(z: Z): BreakInner -> BreakInner:{ .z: read/imm Z -> z } }
"""));}
@Test void mustImplementMethodsInInlineDecOk(){ok(List.of("""
A:{ .foo: A }
Bs:{ #: B -> B: A{'b .foo -> b } }
"""));}
@Test void mustImplementMethodsInInlineDecFail(){fail("""
002| Bs:{ #: B -> B: A{} }
   |      --------^^^^^^

While inspecting object literal "iso B" > "#" line 2
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "A".
Hint: add an implementation for ".foo" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso B:A{}
""", List.of("""
A:{ .foo: A }
Bs:{ #: B -> B: A{} }
"""));}
@Test void mustImplementMethodsInLambdaOk(){ok(List.of("""
A:{ .foo: A }
B:A{}
Bs:{ #: B -> B{'b .foo -> b } }
"""));}
@Test void mustImplementMethodsInLambdaFail(){fail("""
003| Bs:{ #: B -> B{} }
   |      --------^^-

While inspecting object literal instance of "iso B" > "#" line 3
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "A".
Hint: add an implementation for ".foo" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso B
""", List.of("""
A:{ .foo: A }
B:A{}
Bs:{ #: B -> B{} }
"""));}
@Test void fileLogNamedAfterItsType(){ok(List.of("""
PkgLog: base.FileLog{ .name -> base.Nope! }
AppLog: base.FileLog{ .name -> base.Nope! }
Applog: base.FileLog{ .name -> base.Nope! }
"""));}
@Test void fileLogNamedAfterAWindowsReservedDeviceName(){failWf("""
001| Con: base.FileLog{ .name -> base.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Con"
Type declaration "Con" implements "base.FileLog", so it writes to the log file ".out/logs/_p/con.log".
"con" is a Windows reserved device name.
Rename "Con", so that its log file has a name allowed in a Fearless project.
""", List.of("""
Con: base.FileLog{ .name -> base.Nope! }
"""));}
@Test void fileLogWithAnUnderscoreBeforeALowercaseLetter(){failWf("""
001| Foo_bar: base.FileLog{ .name -> base.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Foo_bar"
Type declaration "Foo_bar" implements "base.FileLog", so it writes to a log file named after it.
Type name "Foo_bar" has no file name.
The name of a "base.FileLog" type can only use letters, digits and underscores, and an underscore cannot be followed by a lowercase letter.
""", List.of("""
Foo_bar: base.FileLog{ .name -> base.Nope! }
"""));}
@Test void fileLogWithAPrime(){failWf("""
001| Log': base.FileLog{ .name -> base.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Log'"
Type declaration "Log'" implements "base.FileLog", so it writes to a log file named after it.
Type name "Log'" has no file name.
The name of a "base.FileLog" type can only use letters, digits and underscores, and an underscore cannot be followed by a lowercase letter.
""", List.of("""
Log': base.FileLog{ .name -> base.Nope! }
"""));}
@Test void fileLogNamedLikeARankFile(){failWf("""
001| _RankX: base.FileLog{ .name -> base.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "_RankX"
Type declaration "_RankX" implements "base.FileLog", so it writes to the log file ".out/logs/_p/_rank_x.log".
Only rank files can start with "_rank_".
Rename "_RankX", so that its log file has a name allowed in a Fearless project.
""", List.of("""
_RankX: base.FileLog{ .name -> base.Nope! }
"""));}
@Test void fileLogWithALogPathLongerThan200Characters(){failWf("""
001| Longongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongong: base.FileLog{ .name -> base.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Longongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongong"
Type declaration "Longongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongong" implements "base.FileLog", so it writes to the log file ".out/logs/_p/longongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongong.log".
The path is longer than 200 characters.
Rename "Longongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongong", so that its log file has a name allowed in a Fearless project.
""", List.of("""
Longongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongongong: base.FileLog{ .name -> base.Nope! }
"""));}
@Test void mainWithGenericParameters(){failWf("""
001| Hello[X]: base.Main{ .main -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Hello[_]"
Type declaration "Hello[_]" implements "base.Main" and has generic type parameters.
A type implementing "base.Main" must have zero generic type parameters.
""", List.of("""
Hello[X]: base.Main{ .main -> base.Void }
"""));}
@Test void abstractMainWithGenericParameters(){failWf("""
001| Runner[X]: base.Main{ .go: X }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Runner[_]"
Type declaration "Runner[_]" implements "base.Main" and has generic type parameters.
A type implementing "base.Main" must have zero generic type parameters.
""", List.of("""
Runner[X]: base.Main{ .go: X }
"""));}
@Test void namedMainInAGenericMethod(){failWf("""
001| Box: { .mk[X]: base.Main -> Free[X]: base.Main{ .main -> base.Void{}; .id(y: X): X -> y } }
   |                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal "Free[_]"
Object literal "Free[_]" implements "base.Main" and has generic type parameters.
A type implementing "base.Main" must have zero generic type parameters.
""", List.of("""
Box: { .mk[X]: base.Main -> Free[X]: base.Main{ .main -> base.Void{}; .id(y: X): X -> y } }
"""));}
@Test void anonymousMainInAGenericMethod(){failWf("""
001| Box: { .mk[X]: base.Main -> { .main -> base.Void{}; .id(y: X): X -> y } }
   |                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.Main"
Object literal instance of "base.Main" implements "base.Main" and has generic type parameters.
A type implementing "base.Main" must have zero generic type parameters.
""", List.of("""
Box: { .mk[X]: base.Main -> { .main -> base.Void{}; .id(y: X): X -> y } }
"""));}
@Test void attenuatorWithGenericParameters(){failWf("""
001| NoGui[X]: base.SystemAttenuator{ # -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "NoGui[_]"
Type declaration "NoGui[_]" implements "base.SystemAttenuator" and has generic type parameters.
A concrete type implementing "base.SystemAttenuator" must have zero generic type parameters.
""", List.of("""
NoGui[X]: base.SystemAttenuator{ # -> base.Void }
"""));}
@Test void abstractAttenuatorWithGenericParameters(){ok(List.of("""
Shape[X]: base.SystemAttenuator{ .extra: X }
"""));}
@Test void infoMainWithGenericParameters(){failWf("""
001| Twice[X]: base.InfoMain{ .main -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Twice[_]"
Type declaration "Twice[_]" implements "base.InfoMain" and has generic type parameters.
A concrete type implementing "base.InfoMain" must have zero generic type parameters.
""", List.of("""
Twice[X]: base.InfoMain{ .main -> base.Void }
"""));}
@Test void abstractInfoMainWithGenericParameters(){ok(List.of("""
Shape[X]: base.InfoMain{ .extra: X }
"""));}
@Test void dataReadWithGenericParameters(){failWf("""
001| Pub[X]: base.DataRead{}
   | ^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Pub[_]"
Type declaration "Pub[_]" implements "base.DataRead" and has generic type parameters.
A concrete type implementing "base.DataRead" must have zero generic type parameters.
""", List.of("""
Pub[X]: base.DataRead{}
"""));}
@Test void dataEditWithGenericParameters(){failWf("""
001| Diary[X]: base.DataEdit{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Diary[_]"
Type declaration "Diary[_]" implements "base.DataRead" and has generic type parameters.
A concrete type implementing "base.DataRead" must have zero generic type parameters.
""", List.of("""
Diary[X]: base.DataEdit{}
"""));}
@Test void abstractDataReadWithGenericParameters(){ok(List.of("""
Shape[X]: base.DataRead{ .extra: X }
"""));}
@Test void finalMethodImplementedBelowTheOrigin(){failWf("""
001| Fake: base.DataRead{ .name -> base.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Fake"
Type declaration "Fake" implements method ".name".
"base.Named" implements `base.Final[".name"]` and type declaration "Fake" implements "base.Named",
thus type declaration "Fake" cannot override any method named ".name".
""", List.of("""
Fake: base.DataRead{ .name -> base.Nope! }
"""));}
@Test void finalMethodImplementedInALiteral(){failWf("""
001| Forge: { #: base.DataRead -> base.DataRead{ .name -> base.Nope! } }
   |                              ^^^^^^^^^^^^^^

While inspecting object literal instance of "base.DataRead"
Object literal instance of "base.DataRead" implements method ".name".
"base.Named" implements `base.Final[".name"]` and object literal instance of "base.DataRead" implements "base.Named",
thus object literal instance of "base.DataRead" cannot override any method named ".name".
""", List.of("""
Forge: { #: base.DataRead -> base.DataRead{ .name -> base.Nope! } }
"""));}
@Test void finalCoversEveryArityOfItsName(){failWf("""
002| B: A{ .foo(x: A): A -> x }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Type declaration "B" implements method ".foo(_)".
"A" implements `base.Final[".foo"]` and type declaration "B" implements "A",
thus type declaration "B" cannot override any method named ".foo".
""", List.of("""
A: base.Final[".foo"]{ .foo: A -> this; }
B: A{ .foo(x: A): A -> x }
"""));}
@Test void finalMethodsAreImplementedByTheOriginAndInheritedBelowIt(){ok(List.of("""
A: base.Final[".foo"]{ .foo: A -> this; .foo(x: A): A -> x; }
B: A{ .bar: A -> this; }
C: base.Final["+"]{ +(c: C): C -> c; }
D: base.Final[`.foo`]{ .foo: D }
"""));}
@Test void finalOnAnInheritedMethodLetsTheTypeImplementingFinalImplementIt(){ok(List.of("""
A:{ .foo: A -> this }
B: A, base.Final[".foo"]{ .foo: A -> this }
C: B{}
"""));}
@Test void finalTakesAMethodName(){failWf("""
001| A: base.Final["foo"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.Final["foo"]`.
The generic type argument of "base.Final[_]" is a string literal type holding a method name, like `".name"` or `"+"`.
""", List.of("""
A: base.Final["foo"]{}
"""));}
@Test void finalTakesAStringLiteralType(){failWf("""
001| A: base.Final[A]{}
   | ^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.Final[A]".
The generic type argument of "base.Final[_]" is a string literal type holding a method name, like `".name"` or `"+"`.
""", List.of("""
A: base.Final[A]{}
"""));}
@Test void fileLogWithGenericParameters(){failWf("""
001| MyLog[X]: base.FileLog{ .name -> base.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "MyLog[_]"
Type declaration "MyLog[_]" implements "base.FileLog" and has generic type parameters.
A concrete type implementing "base.FileLog" must have zero generic type parameters.
""", List.of("""
MyLog[X]: base.FileLog{ .name -> base.Nope! }
"""));}
@Test void inMemoryLogWithGenericParameters(){failWf("""
001| Steps[X]: base.InMemoryLog[X]{ .name -> base.Nope! }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Steps[_]"
Type declaration "Steps[_]" implements "base.InMemoryLog[_]" and has generic type parameters.
A concrete type implementing "base.InMemoryLog[_]" must have zero generic type parameters.
""", List.of("""
Steps[X]: base.InMemoryLog[X]{ .name -> base.Nope! }
"""));}
@Test void anonymousInMemoryLogInAGenericMethod(){failWf("""
001| Box: { .mk[X]: base.InMemoryLog[X] -> { .name -> base.Nope! } }
   |                                       ^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.InMemoryLog[_]"
Object literal instance of "base.InMemoryLog[_]" implements "base.InMemoryLog[_]" and has generic type parameters.
A concrete type implementing "base.InMemoryLog[_]" must have zero generic type parameters.
""", List.of("""
Box: { .mk[X]: base.InMemoryLog[X] -> { .name -> base.Nope! } }
"""));}
@Test void concreteLogsOfConcreteTypes(){ok(List.of("""
Steps: base.InMemoryLog[Steps]{ .name -> base.Nope! }
Shape[X]: base.InMemoryLog[X]{ .extra: X }
Box: { .mk[X]: base.InMemoryLog[Steps] -> { .name -> base.Nope! } }
"""));}
@Test void openWithWithoutMain(){failWf("""
001| Assoc: base.OpenWith[Icon,"foo"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Assoc"
Type declaration "Assoc" implements "base.OpenWith[_,_]".
Only a main can implement "base.OpenWith[_,_]": type declaration "Assoc" must also implement "base.Main", directly or through one of its supertypes.
""", List.of("""
Assoc: base.OpenWith[Icon,"foo"]{}
Icon: {}
"""));}
@Test void openWithTwice(){failWf("""
001| Two: base.Main, base.OpenWith[Icon,"foo"], base.Shortcut[Icon,"fapp001"], base.OpenWith[Icon2,"foo"]{ .main -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Two"
Type declaration "Two" claims the extension "foo" more than once:
both `base.OpenWith[Icon,"foo"]` and `base.OpenWith[Icon2,"foo"]` claim it.
A main can claim each extension at most once, across all its "base.OpenWith[_,_]" and "base.Shortcut[_,_]", since one extension has one icon.
""", List.of("""
Two: base.Main, base.OpenWith[Icon,"foo"], base.Shortcut[Icon,"fapp001"], base.OpenWith[Icon2,"foo"]{ .main -> base.Void }
Icon: {}
Icon2: {}
"""));}
@Test void openWithIconNotConcrete(){failWf("""
001| One: base.Main, base.OpenWith[Box[Icon],"foo"]{ .main -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "One"
Type declaration "One" implements `base.OpenWith[Box[Icon],"foo"]`.
"Box[Icon]" is not a valid icon.
Only concrete types with zero generic type arguments are valid icons.
""", List.of("""
One: base.Main, base.OpenWith[Box[Icon],"foo"]{ .main -> base.Void }
Box[X]: {}
Icon: {}
"""));}
@Test void openWithExtensionNotAString(){failWf("""
001| One: base.Main, base.OpenWith[Icon,Icon]{ .main -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "One"
Type declaration "One" implements "base.OpenWith[Icon,Icon]".
The extension "Icon" is not a string literal type.
An extension is written as a string literal type, like `"ffile347"`, `"xml"` or `"txt"`; or implement "base.OpenWith[_]" to let the Fearless manager choose one.
""", List.of("""
One: base.Main, base.OpenWith[Icon,Icon]{ .main -> base.Void }
Icon: {}
"""));}
@Test void openWithInvalidExtension(){failWf("""
001| One: base.Main, base.OpenWith[Icon,"Foo"]{ .main -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "One"
Type declaration "One" implements `base.OpenWith[Icon,"Foo"]`.
"Foo" is not a valid extension.
An extension is 1 to 16 characters, each a lowercase letter "a"-"z" or a digit "0"-"9", with no dot; or implement "base.OpenWith[_]" to let the Fearless manager choose one.
""", List.of("""
One: base.Main, base.OpenWith[Icon,"Foo"]{ .main -> base.Void }
Icon: {}
"""));}
@Test void shortcutNotFapp(){failWf("""
001| One: base.Main, base.Shortcut[Icon,"foo"]{ .main -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "One"
Type declaration "One" implements `base.Shortcut[Icon,"foo"]`.
"foo" is not a shortcut extension: a shortcut file only starts its main, so it must not look like a document of another program or a file of the project.
A shortcut extension is "fapp" followed by three digits, like "fapp042"; or implement "base.Shortcut[_]" to let the Fearless manager choose one.
""", List.of("""
One: base.Main, base.Shortcut[Icon,"foo"]{ .main -> base.Void }
Icon: {}
"""));}
@Test void openWithFapp(){failWf("""
001| One: base.Main, base.OpenWith[Icon,"fapp001"]{ .main -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "One"
Type declaration "One" implements `base.OpenWith[Icon,"fapp001"]`.
"fapp001" is a shortcut extension: "fapp" followed by three digits names the shortcut files of the Fearless manager.
Use an extension of the form "ffile" followed by three digits, like "ffile042", or a system extension, like "htm"; or implement "base.OpenWith[_]" to let the Fearless manager choose one.
""", List.of("""
One: base.Main, base.OpenWith[Icon,"fapp001"]{ .main -> base.Void }
Icon: {}
"""));}
@Test void sealedOutsidePkg(){failWf("""
001| C:base.Void{}
   | ^^^^^^^^^^^^^

While inspecting type declaration "C"
Type declaration "C" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Type declaration "C" is in package "p".
Type "base.Void" is in package "base".
""", List.of("""
C:base.Void{}
"""));}
@Test void sealedOutsidePkgInline(){failWf("""
001| Test:{ #: C -> C: base.Void{} }
   |                ^^^^^^^^^^^^^^

While inspecting object literal "C"
Object literal "C" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Object literal "C" is in package "p".
Type "base.Void" is in package "base".
""", List.of("""
Test:{ #: C -> C: base.Void{} }
"""));}
@Test void sealedOutsidePkgMultiImpl(){failWf("""
002| Test:{ #: C -> C: base.Void,A{} }
   |                ^^^^^^^^^^^^^^^^

While inspecting object literal "C"
Object literal "C" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Object literal "C" is in package "p".
Type "base.Void" is in package "base".
""", List.of("""
A:{}
Test:{ #: C -> C: base.Void,A{} }
"""));}
@Test void sealedWithinPkg(){ok(List.of("""
Sealed:{}
A:Sealed{}
B:A{}
"""));}
@Test void sealedOutsidePkgUsedThroughAConstructor(){ok(List.of("""
C:{ .foo: base.Void -> base.Void }
"""));}
@Test void allowPrivateLambdaUsageWithinPkg(){ok(List.of("""
_RootCap:{}
Good:{ .ok: mut _RootCap -> {} }
"""));}
@Test void noPrivateNameFromAnotherPkg(){failParse("""
001| A:{ #: base._RootCap -> {} }
   |     ~~~^^^^^^^^^^^^^------

While inspecting method signature > method declaration > type declaration body > type declaration > full file
Code is attempting to use private name "_RootCap" from package "base".
Type names starting with "_" can only be used in their own package, and only by their simple name.
""", List.of("""
A:{ #: base._RootCap -> {} }
"""));}
@Test void mutTypeWithGenericArgument(){ok(List.of("""
A[X:*]:{ .no: mut A[X] }
"""));}
@Test void readTypeNestedInReadType(){ok(List.of("""
A[X:*]:{ .no: read A[read A[X]] }
"""));}
@Test void objectLiteralImplementingAForeignSealedTypeThroughAnAlias(){failWf("""
002| Test:{ #: C -> C: V{} }
   |                ^^^^^^

While inspecting object literal "C"
Object literal "C" implements sealed type "V".
Sealed types can only be implemented in their own package.
Object literal "C" is in package "p".
Type "V" is in package "base".
""", List.of("""
use base.Void as V;
Test:{ #: C -> C: V{} }
"""));}
@Test void supertypeWrittenTwice(){failWf("""
001| A:B,C,B,D{}
   | ^^^^^^^^^^^

While inspecting type declaration "A"
Duplicate supertype in type declaration: "B".
Remove one of them.
""", List.of("""
A:B,C,B,D{}
B:{}
C:{}
D:{}
"""));}
@Test void supertypeWithAndWithoutDefaultImm(){failWf("""
003| B:A[Foo],A[imm Foo]{}
   | ^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Duplicate supertype in type declaration: "A[Foo]" and "A[imm Foo]" denote the same type.
Remove one of them.
""", List.of("""
Foo:{}
A[X:*]:{}
B:A[Foo],A[imm Foo]{}
"""));}
@Test void supertypeTypeVariableWithAndWithoutRedundantRc(){failWf("""
002| A[Y:imm]:Foo[Y],Foo[imm Y]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Duplicate supertype in type declaration: "Foo[Y]" and "Foo[imm Y]" denote the same type.
Remove one of them.
""", List.of("""
Foo[T:*]:{ .get: T }
A[Y:imm]:Foo[Y],Foo[imm Y]{}
"""));}
@Test void supertypeNestedTypeVariableWithAndWithoutRedundantRc(){failWf("""
[###]
Duplicate supertype in type declaration: "Foo[Box[read Y]]" and "Foo[Box[Y]]" denote the same type.
Remove one of them.
""", List.of("""
Box[T:*]:{}
Foo[T:*]:{}
A[Y:read]:Foo[Box[read Y]],Foo[Box[Y]]{}
"""));}
@Test void supertypeTypeVariableWithNonRedundantRcOk(){ok(List.of("""
Foo[T:*]:{}
A[Y:imm,mut]:Foo[Y],Foo[imm Y]{}
"""));}
@Test void supertypeSimpleAndQualified(){failWf("""
002| B:A,p.A{}
   |     ^^^^

While inspecting a type name
The full type name "p.A" is invalid in source code inside folders named "_p".
Source code inside folders named "_p" uses the simple name "A" to refer to "p.A".
""", List.of("""
A:{}
B:A,p.A{}
"""));}
@Test void supertypeUseAliasAndQualified(){failWf("""
002| B:CF,base.CaptureFree{}
   |      ^^^^^^^^^^^^^^^^^

While inspecting a type name
The full type name "base.CaptureFree" is invalid in source code inside folders named "_p".
Source code inside folders named "_p" uses the simple name "CF" to refer to "base.CaptureFree", because of "use base.CaptureFree as CF".
""", List.of("""
use base.CaptureFree as CF;
B:CF,base.CaptureFree{}
"""));}
@Test void supertypeDifferentSpellingOfTypeArgument(){failWf("""
003| B:A[Foo],A[p.Foo]{}
   |            ^^^^^^

While inspecting a type name
The full type name "p.Foo" is invalid in source code inside folders named "_p".
Source code inside folders named "_p" uses the simple name "Foo" to refer to "p.Foo".
""", List.of("""
Foo:{}
A[X:*]:{}
B:A[Foo],A[p.Foo]{}
"""));}
@Test void directivesOutsideTheRankFile(){failWf("""
001| use base.Nat as N;
   |     ^^^^^^^^

While inspecting the file
Package directives outside of rank file.
Only the rank file can contain directives like maps and uses.

Found non-empty:
- uses: use base.Nat as N
""", List.of("""
A:{}
""", """
use base.Nat as N;
B:{}
"""));}
@Test void directivesOutsideTheRankFileAfterAComment(){failWf("""
002| use base.Nat as N;
   |     ^^^^^^^^

While inspecting the file
Package directives outside of rank file.
Only the rank file can contain directives like maps and uses.

Found non-empty:
- maps: map a as _p in _q
- uses: use base.Nat as N
""", List.of("""
A:{}
""", """
//the header
use base.Nat as N;
map a as _p in _q;
B:{}
"""));}
@Test void mapDirectiveOutsideTheRankFileAfterAComment(){failWf("""
002| map a as _p in _q;
   |     ^

While inspecting the file
Package directives outside of rank file.
Only the rank file can contain directives like maps and uses.

Found non-empty:
- maps: map a as _p in _q
- uses: use base.Nat as N
""", List.of("""
A:{}
""", """
//the header
map a as _p in _q;
use base.Nat as N;
B:{}
"""));}
@Test void useTwiceTheSameSource(){failParse("""
001| use base.Nat as N;
002| use base.Nat as M;
   | ----------------^

While inspecting header element > file header > full file
The directive "use base.Nat as M" clashes with the earlier "use base.Nat as N".
""", List.of("""
use base.Nat as N;
use base.Nat as M;
A:{}
"""));}
@Test void useTwiceTheSameDestination(){failParse("""
001| use base.Nat as N;
002| use base.Str as N;
   | ----------------^

While inspecting header element > file header > full file
The directive "use base.Str as N" clashes with the earlier "use base.Nat as N".
""", List.of("""
use base.Nat as N;
use base.Str as N;
A:{}
"""));}
@Test void mapTwiceTheSameNameInTheSamePackage(){failParse("""
001| map foo as _base in _p;
002| map foo as _base in _p;
   | --------------------^^

While inspecting header element > file header > full file
There is already a map of package name "foo" for source code inside folders named "_p".
""", List.of("""
map foo as _base in _p;
map foo as _base in _p;
A:{}
"""));}
@Test void typeParameterNamedAsAUseDestination(){failWf("""
002| A[X]:{}
   |   ^

While inspecting a type name
Generic type parameter "X" is declared in package "p".
Name "X" is also used in a "use" directive.
""", List.of("""
use base.Nat as X;
A[X]:{}
"""));}
@Test void finalOfATypeParameter(){failWf("""
001| A[X]: base.Final[X]{}
   | ^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Type declaration "A[_]" implements "base.Final[X]".
The generic type argument of "base.Final[_]" is a string literal type holding a method name, like `".name"` or `"+"`.
""", List.of("""
A[X]: base.Final[X]{}
"""));}
@Test void widenToTwice(){failWf("""
001| A: base.WidenTo[A], base.WidenTo[base.Nat]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.WidenTo[_]" more than once.
At most one "base.WidenTo[_]" supertype is allowed, because it defines the preferred widened type.

Found the following "base.WidenTo[_]" supertypes:
- "base.WidenTo[A]"
- "base.WidenTo[base.Nat]"
""", List.of("""
A: base.WidenTo[A], base.WidenTo[base.Nat]{}
"""));}
@Test void openWithIconATypeParameter(){failWf("""
002| M[X]: base.Main, base.OpenWith[X,"foo"]{ .main -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "M[_]"
Type declaration "M[_]" implements `base.OpenWith[X,"foo"]`.
"X" is not a valid icon.
Only concrete types with zero generic type arguments are valid icons.
""", List.of("""
Icon:{}
M[X]: base.Main, base.OpenWith[X,"foo"]{ .main -> base.Void }
"""));}
@Test void openWithExtensionFearless(){failWf("""
002| M: base.Main, base.OpenWith[Icon,"fearless"]{ .main -> base.Void }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "M"
Type declaration "M" implements `base.OpenWith[Icon,"fearless"]`.
"fearless" is not a valid extension.
The extension "fearless" is reserved; or implement "base.OpenWith[_]" to let the Fearless manager choose one.
""", List.of("""
Icon:{}
M: base.Main, base.OpenWith[Icon,"fearless"]{ .main -> base.Void }
"""));}
@Test void finalMethodImplementedBelowTheFinalTypeWithAnotherFinal(){failWf("""
002| B: base.Final[".b"], A{ .b: B -> this; .a: A -> this }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Type declaration "B" implements method ".a".
"A" implements `base.Final[".a"]` and type declaration "B" implements "A",
thus type declaration "B" cannot override any method named ".a".
""", List.of("""
A: base.Final[".a"]{ .a: A -> this }
B: base.Final[".b"], A{ .b: B -> this; .a: A -> this }
"""));}
@Test void twoRankFiles(){typeFailRaw("""
Ambiguous rank file for package "p".
Found 2 files that look like rank head candidates:
- fear:/___DBG___/_rank_app999.fear
- fear:/___DBG___/_rank_other000.fear
There must be exactly one source file whose name represents this package rank.
Rename or remove the extra files so that only one file name is of form "_rank_*.fear".
Every package must declare its rank: base, core, driver, worker, framework, accumulator, tool, or app.
The rank file is the file whose name matches the rank name.

For example, for an application you would typically have a file named
  "_rank_app.fear"
Other examples: "_rank_driver.fear", "_rank_framework.fear" or "_rank_app175.fear"; with explicit rank number.
As a rule of thumb: final applications use appNNN; shared libraries often use workerNNN or frameworkNNN.
Error 7 WellFormedness""", SourceOracle.debugBuilder().put(0, "A:{}").putURI(URI.create("fear:/___DBG___/_rank_other000.fear"), "B:{}").build());}
@Test void noRankFile(){typeFailRaw("""
No rank file found for package "p".
Each package must have exactly one source file whose name is its rank,
in some folder inside the project folder.
Every package must declare its rank: base, core, driver, worker, framework, accumulator, tool, or app.
The rank file is the file whose name matches the rank name.

For example, for an application you would typically have a file named
  "_rank_app.fear"
Other examples: "_rank_driver.fear", "_rank_framework.fear" or "_rank_app175.fear"; with explicit rank number.
As a rule of thumb: final applications use appNNN; shared libraries often use workerNNN or frameworkNNN.
Error 7 WellFormedness""", SourceOracle.debugBuilder().put(1, "A:{}").build());}
@Test void claimsWithoutExtension(){ok(List.of("""
Icon:{}
M: base.Main, base.OpenWith[Icon], base.Shortcut[Icon], base.PreLoadIcon[Icon]{ .main -> base.Void }
"""));}
}
