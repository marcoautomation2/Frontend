package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public final class MethodCompositionTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }
  static void failWf(String expected, List<String> input){
    typeFailRaw("In file: [###].fear\n\n"+expected+"Error 7 WellFormedness", input);
  }

@Test void noMeths(){ok(List.of("""
A:{}
"""));}
@Test void oneMeth(){ok(List.of("""
A:{ .foo(a:A):A->this }
"""));}
@Test void twoMethOneAbs(){ok(List.of("""
A:{ .foo(a:A):A->this; .bar(a1: A, a2: read A): mut A }
"""));}
@Test void twoMethBothImpl(){ok(List.of("""
A:{ .foo(a:A):A->this; .bar(a1: A, a2: read A): mut A->{} }
"""));}
@Test void oneAbs(){ok(List.of("""
A:{ .foo(a:A):A }
"""));}
@Test void noOverride(){ok(List.of("""
A:{ .foo(a:A):A }
B:A{ .bar(b:B):B }
"""));}
@Test void sameMeth(){ok(List.of("""
A:{ .foo(a:A):A }
B:A{ .foo(b:A):A }
"""));}
@Test void refineRt(){ok(List.of("""
A:{ .foo(a:A):A }
B:A{ .foo(b:A):B }
"""));}
@Test void refineRtAndStrengthenParam(){fail("""
003| B:A{ .foo(b:B):Int }
   | -----^^^^^^^^^^^^^--

While inspecting type declaration "B"
Invalid method signature for "B.foo(_)".
The method ".foo(_)" accepts parameter 1 of type "B".
But "A.foo(_)" requires "A", which is not a subtype of "B".
It is instead a supertype: you are strengthening the parameter instead of weakening it.
""", List.of("""
Str:{} Int:{}
A:{ .foo(a:A):Str }
B:A{ .foo(b:B):Int }
"""));}
@Test void ownMethodStrengthensParamOfBothSupers(){fail("""
001| A:B,C{ .foo(a:A):A }
   | -------^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.foo(_)".
The method ".foo(_)" accepts parameter 1 of type "A".
But "B.foo(_)" requires "B", which is not a subtype of "A".
It is instead a supertype: you are strengthening the parameter instead of weakening it.
""", List.of("""
A:B,C{ .foo(a:A):A }
B:{ .foo(b:B):B }
C:{ .foo(c:C):C }
"""));}
@Test void refineRtOnly(){ok(List.of("""
A:B{ .m: A }
B:{ .m: B }
"""));}
@Test void sameRt(){ok(List.of("""
Int:{}
A:B{ .m: Int }
B:{ .m: Int }
"""));}
@Test void unrelatedRt(){fail("""
002| A:B{ .m: Str }
   | -----^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Str".
But "B.m" returns type "Int", which is not a supertype of "Str".
The two types are unrelated.
""", List.of("""
Int:{} Str:{}
A:B{ .m: Str }
B:{ .m: Int }
"""));}
@Test void twoSupersPickedByOwnMeth(){ok(List.of("""
A:B,C{ .m: A }
B:{ .m: B }
C:{ .m: C }
"""));}
@Test void twoSupersDisagreeOnRt(){failWf("""
001| A:B,C{}
   | ^^^^^^^

While inspecting type declaration "A"
Supertypes disagree on the return type of method "imm .m" with 0 parameters.
Candidates:
- "B"
- "C"
Type declaration "A" must declare a method ".m" explicitly choosing the desired option.
""", List.of("""
A:B,C{}
B:{ .m: B }
C:{ .m: C }
"""));}
@Test void twoSupersDisagreeOnRtInherited(){failWf("""
003| AA:B,C{}
   | ^^^^^^^^

While inspecting type declaration "AA"
Supertypes disagree on the return type of method "imm .m" with 0 parameters.
Candidates:
- "B"
- "C"
Type declaration "AA" must declare a method ".m" explicitly choosing the desired option.
""", List.of("""
A:AA{ .m: Int }
Int:{}
AA:B,C{}
B:{ .m: B }
C:{ .m: C }
"""));}
@Test void threeSupersPickedByOwnMeth(){ok(List.of("""
A:B,C,D{ .m: A }
B:{ .m: B }
C:{ .m: C }
D:{ .m: D }
"""));}
@Test void threeSupersPickedMostSpecific(){ok(List.of("""
A:B,C,D{ .m: B }
B:D{ .m: D }
C:D{ .m: D }
D:{ .m: D }
"""));}
@Test void threeSupersPickedLessSpecific(){fail("""
001| A:B,C,D{ .m: D }
   | ---------^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "D".
But "B.m" returns type "B", which is not a supertype of "D".
It is instead a subtype: you are weakening the result instead of strengthening it.
""", List.of("""
A:B,C,D{ .m: D }
B:D{ .m: B }
C:D{ .m: B }
D:{ .m: B }
"""));}
@Test void sameNameDifferentArities(){fail("""
002| A[X:*]:A[X,X]{ .m(b:A):A }
   | ---------------^^^^^^^^^--

While inspecting type declaration "A[_]"
Invalid method signature for "A[_].m(_)".
The method ".m(_)" returns type "A".
But "A[_,_].m(_)" returns type "A[X,X]", which is not a supertype of "A".
The two types are unrelated.
""", List.of("""
A:A[A],A[A,A]{ .m(a:A):A }
A[X:*]:A[X,X]{ .m(b:A):A }
A[X:*,Y:*]:{ .m(c:A):A[X,Y] }
"""));}
@Test void bothSupersAbstract(){ok(List.of("""
Foo:{}
A:B,C{}
B:{ .m(b:Foo): Foo }
C:{ .m(c:Foo): Foo }
"""));}
@Test void firstSuperImplements(){ok(List.of("""
Foo:{}
A:B,C{}
B:{ .m(b:Foo): Foo -> b }
C:{ .m(c:Foo): Foo }
"""));}
@Test void secondSuperImplements(){ok(List.of("""
Foo:{}
A:B,C{}
B:{ .m(b:Foo): Foo }
C:{ .m(c:Foo): Foo -> c }
"""));}
@Test void bothSupersImplement(){failWf("""
002| A:B,C{}
   | ^^^^^^^

While inspecting type declaration "A"
Ambiguous implementation for method ".m(_)" with 1 parameter.
Implemented by the supertypes:
- "B"
- "C"
Type declaration "A" must declare a method ".m(_)" explicitly implementing the desired behaviour.
""", List.of("""
Foo:{}
A:B,C{}
B:{ .m(b:Foo): Foo -> b }
C:{ .m(c:Foo): Foo -> c }
"""));}
@Test void reAbstractedImplBesideAnotherImpl(){ok(List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
C:B{ .m: R; }
D:A,C{}
"""));}
@Test void inheritedImplBesideAnotherImpl(){failWf("""
005| D:A,C{}
   | ^^^^^^^

While inspecting type declaration "D"
Ambiguous implementation for method ".m" with 0 parameters.
Implemented by the supertypes:
- "A"
- "B"
Type declaration "D" must declare a method ".m" explicitly implementing the desired behaviour.
""", List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
C:B{}
D:A,C{}
"""));}
@Test void bothSupersInheritTheSameImpl(){ok(List.of("""
Foo:{}
A:B,C{}
B:D{ .m(b:Foo): Foo }
C:D{ .m(c:Foo): Foo }
D:{ .m(d:Foo): Foo -> d }
"""));}
@Test void genericSupersAgreeOnRt(){ok(List.of("""
A:B[A],C[List[A]]{}
B[X:*]:{ .m: List[X] }
C[Y:*]:{ .m: Y }
List[T:*]:{}
"""));}
@Test void genericSupersAgreeOnRtAndOnSharedSuper(){ok(List.of("""
A:B[A],C[List[A]]{}
B[X:*]:K[List[X]]{ .m: List[X] }
C[Y:*]:K[Y]{ .m: Y }
K[Y:*]:{ .kk: Y }
List[T:*]:{}
"""));}
@Test void genericSupersDisagreeOnSharedSuperArgs(){failWf("""
001| A:B[A],C[List[A]]{}
   | ^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Supertypes disagree on the return type of method "imm .kk" with 0 parameters.
Candidates:
- "A"
- "List[A]"
Type declaration "A" must declare a method ".kk" explicitly choosing the desired option.
""", List.of("""
A:B[A],C[List[A]]{}
B[X:*]:K[X]{ .m: List[X] }
C[Y:*]:K[Y]{ .m: Y }
K[Y:*]:{ .kk: Y }
List[T:*]:{}
"""));}
@Test void genericSupersDisagreeButSharedMethIsConcrete(){ok(List.of("""
A:B[A],C[List[A]]{}
B[X:*]:K[X]{ .m: List[X] }
C[Y:*]:K[Y]{ .m: Y }
K[Y:*]:{ .kk: A }
List[T:*]:{}
"""));}
@Test void genericSupersAgreeAndSharedMethIsConcrete(){ok(List.of("""
A:B[A],C[List[A]]{}
B[X:*]:K[List[X]]{ .m: List[X] }
C[Y:*]:K[Y]{ .m: Y }
K[Y:*]:{ .kk: A }
List[T:*]:{}
"""));}
@Test void overrideInheritsTheSuperTypeParameters(){ok(List.of("""
Foo:{}
A:B{ .m: Foo }
B:{ .m[X:*]: Foo }
C:{ .withTArg(a:A): Foo -> a.m[Foo]; .noTArg(a:A): Foo -> a.m }
"""));}
@Test void overrideCanNotNameTheInheritedTypeParameter(){failWf("""
002| A:B{ .m(x: X): Foo }
   |            ^

While inspecting a type name
Type "X" is not declared in package "p" and is not made visible via "use".
In scope:
- "A"
- "B"
- "Foo"
""", List.of("""
Foo:{}
A:B{ .m(x: X): Foo }
B:{ .m[X:*](x: X): Foo }
"""));}
@Test void overrideDeclaresTooManyTypeParametersForTwoSupertypes(){failWf("""
002| A:B,C{ .m[X:*,Y:*]: Foo }
   |        ^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" declares 2 generic type parameters, but these supertypes declare 1:
- "B"
- "C"
""", List.of("""
Foo:{}
A:B,C{ .m[X:*,Y:*]: Foo }
B:{ .m[X:*]: Foo }
C:{ .m[Z:*]: Foo }
"""));}
@Test void aMethodUsingTheImplicitParameterWithNoSupertype(){failWf("""
001| A:{ .m -> ::.foo }
   | ----^^^^^^^^^^^^--

While inspecting type declaration "A"
Cannot infer signature of method ".m(_)".
No supertype has a method named ".m(_)" with 1 parameter.
"::" in the body is the parameter of ".m(_)".
""", List.of("""
A:{ .m -> ::.foo }
"""));}
@Test void aMethodUsingAWrittenParameterWithNoSupertype(){failWf("""
001| A:{ .m(x) -> { .k -> ::.foo } }
   | ----^^^^^^^^^^^^^^^^^^^^^^^^^--

While inspecting type declaration "A"
Cannot infer signature of method ".m(_)".
No supertype has a method named ".m(_)" with 1 parameter.
""", List.of("""
A:{ .m(x) -> { .k -> ::.foo } }
"""));}
@Test void overrideDeclaresTooManyTypeParameters(){failWf("""
002| A:B{ .m[X:*,Y:*]: Foo }
   |      ^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" declares 2 generic type parameters, but supertype "B" declares 1.
""", List.of("""
Foo:{}
A:B{ .m[X:*,Y:*]: Foo }
B:{ .m[X:*]: Foo }
"""));}
@Test void overrideDeclaresNarrowerBounds(){failWf("""
002| A:B{ .m[X:imm]: Foo }
   |      ^^^^^^^^^^^^^^

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" declares different capability bounds than the supertypes for generic type parameter 1.
Local declaration: "X:imm".
Capability bounds in the supertypes: "imm,mut,read".
Generic type parameter names may differ from the supertypes; only the position matters.
""", List.of("""
Foo:{}
A:B{ .m[X:imm]: Foo }
B:{ .m[X:*]: Foo }
"""));}
@Test void classGenericUsedInRefinedRt(){ok(List.of("""
A[X:*]:B{ .foo: imm X }
B:{ .m[X:*]: A[B] }
"""));}
@Test void classGenericPassedToSuperGeneric(){ok(List.of("""
A[X:*]:B[X]{ .foo: imm X }
B[Y:*]:{ .m[X:*]: Bi[imm X,imm Y] }
Bi[AA:*,BB:*]:{}
"""));}
@Test void refineRtGenericArgCovariantIsNotEnough(){fail("""
001| A:B{ .m: Break[A] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[A]".
But "B.m" returns type "Break[B]", which is not a supertype of "Break[A]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[A] }
B:{ .m: Break[B] }
Break[X:*]:{}
"""));}
@Test void refineRtGenericArgContravariant(){fail("""
001| A:B{ .m: Break[B] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[B]".
But "B.m" returns type "Break[A]", which is not a supertype of "Break[B]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[B] }
B:{ .m: Break[A] }
Break[X:*]:{}
"""));}
@Test void refineRtGenericArgCovariantWithGetter(){fail("""
001| A:B{ .m: Break[A] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[A]".
But "B.m" returns type "Break[B]", which is not a supertype of "Break[A]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[A] }
B:{ .m: Break[B] }
Break[X:*]:{ .b: X }
"""));}
@Test void refineRtGenericArgContravariantWithGetter(){fail("""
001| A:B{ .m: Break[B] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[B]".
But "B.m" returns type "Break[A]", which is not a supertype of "Break[B]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[B] }
B:{ .m: Break[A] }
Break[X:*]:{ .b: X }
"""));}
@Test void refineRtGenericArgCovariantRecursive(){fail("""
001| A:B{ .m: Break[A] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[A]".
But "B.m" returns type "Break[B]", which is not a supertype of "Break[A]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[A] }
B:{ .m: Break[B] }
Break[X:*]:{ .b: Break[X] }
"""));}
@Test void refineRtGenericArgContravariantRecursive(){fail("""
001| A:B{ .m: Break[B] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[B]".
But "B.m" returns type "Break[A]", which is not a supertype of "Break[B]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[B] }
B:{ .m: Break[A] }
Break[X:*]:{ .b: Break[X] }
"""));}
@Test void methGens(){ok(List.of("""
A:{
  .m1[T:*](x:T):base.Void->this.m2(x);
  .m2[K:*](k:K):base.Void;
  }
"""));}
@Test void boolPkg(){ok(List.of("""
Bool:Sealed{
  .and(b: Bool): Bool;
  .or(b: Bool): Bool;
  .not: Bool;
  ?[R:*](f: mut ThenElse[R]): R;
  }
Sealed:{}
True:Bool{ .and(b) -> b; .or(b) -> this; .not -> False; ?(f) -> f.then }
False:Bool{ .and(b) -> this; .or(b) -> b; .not -> True; ?(f) -> f.else }
Fresh1:False,Bool{}
Fresh2:Bool,False{}
ThenElse[R:*]:{ mut .then: R; mut .else: R }
"""));}
@Test void namedLiteralKeepsClassGeneric(){ok(List.of("""
List[T:*]:{} Bob:{}
Bar[X:*]:{ .m: Foo[X] -> Foo[X:*]:{} }
"""));}
@Test void genericConflict(){failWf("""
004| D:B,C{}
   | ^^^^^^^

While inspecting type declaration "D"
Supertypes disagree on the type of parameter 1 of method "imm .m(_)" with 1 parameter.
Candidates:
- "base.Int"
- "base.Float"
Type declaration "D" must declare a method ".m(_)" explicitly choosing the desired option.
""", List.of("""
A[X:*]:{ .m(x:X):X->x }
B:A[base.Int]{}
C:A[base.Float]{}
D:B,C{}
"""));}
@Test void reAbstractedMethodListingBothSupers(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
C:A,B{}
"""));}
@Test void reAbstractedMethodListingBothSupersSubFirst(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
C:B,A{}
"""));}
@Test void overriddenMethodListingBothSupers(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A->A }
C:A,B{}
"""));}
@Test void reAbstractedMethodAndInheritedImplementation(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
D:A{}
C:B,D{}
"""));}
@Test void reAbstractedMethodAndInheritedImplementationIsAbstract(){fail("""
004| User:{ #:C->C:B,D{} }
   |        -----^^^^^^^

While inspecting object literal "C" > method "User#" (line 4)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "B".
Hint: add an implementation for ".m" inside the object literal.
""", List.of("""
A:{ .m:A->this }
B:A{ .m:A }
D:A{}
User:{ #:C->C:B,D{} }
"""));}
@Test void reAbstractedMethodAndInheritedImplementationSubLast(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
D:A{}
C:D,B{}
"""));}
@Test void reAbstractedDeepInOneBranch(){fail("""
007| User:{ #:D->D:E,F{} }
   |        -----^^^^^^^

While inspecting object literal "D" > method "User#" (line 7)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "C".
Hint: add an implementation for ".m" inside the object literal.
""", List.of("""
R:{}
A:{ .m: R -> R }
B:A{}
C:B{ .m: R; }
E:C{}
F:A{}
User:{ #:D->D:E,F{} }
"""));}
@Test void reAbstractedSuperBesideImpl(){ok(List.of("""
R:{}
A:{ .m: R -> R }
X:A{ .m: R; }
B:{ .m: R -> R }
User:{ #:D->D:X,B{} }
"""));}
@Test void reAbstractedSuperBesideImplImplFirst(){ok(List.of("""
R:{}
A:{ .m: R -> R }
X:A{ .m: R; }
B:{ .m: R -> R }
User:{ #:D->D:B,X{} }
"""));}
@Test void abstractSuperBesideImplIsInstantiable(){ok(List.of("""
R:{}
B:{ .m: R -> R }
C:{ .m: R; }
User:{ #:A->A:B,C{} }
"""));}
@Test void implBesideTwoAbstractSupers(){ok(List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R; }
C:{ .m: R; }
User:{ #:D->D:B,A,C{} }
"""));}
@Test void reAbstractedImplHiddenInsideAnotherSuper(){ok(List.of("""
R:{}
J:{ .m: R -> R }
X:J{ .m: R; }
I:{ .m: R -> R }
P:X,I{}
Q:J{}
User:{ #:D->D:P,Q{} }
"""));}
@Test void reAbstractedImplHiddenInsideAnotherAbstractSuper(){fail("""
007| User:{ #:D->D:P,Q{} }
   |        -----^^^^^^^

While inspecting object literal "D" > method "User#" (line 7)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "P" and "K" and "X".
Hint: add an implementation for ".m" inside the object literal.
""", List.of("""
R:{}
J:{ .m: R -> R }
X:J{ .m: R; }
K:{ .m: R; }
P:X,K{}
Q:J{}
User:{ #:D->D:P,Q{} }
"""));}
@Test void eachImplReAbstractedByTheOtherBranch(){fail("""
006| User:{ #:D->D:A1,A2{} }
   |        -----^^^^^^^^^

While inspecting object literal "D" > method "User#" (line 6)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "A1" and "A2".
Hint: add an implementation for ".m" inside the object literal.
""", List.of("""
R:{}
I1:{ .m: R -> R }
I2:{ .m: R -> R }
A1:I2{ .m: R; }
A2:I1{ .m: R; }
User:{ #:D->D:A1,A2{} }
"""));}
@Test void eachImplReAbstractedByTheOtherBranchDeclared(){ok(List.of("""
R:{}
I1:{ .m: R -> R }
I2:{ .m: R -> R }
A1:I2{ .m: R; }
A2:I1{ .m: R; }
D:A1,A2{}
"""));}
@Test void implOverriddenByImplInAnotherBranch(){ok(List.of("""
R:{}
J:{ .m: R -> R }
K:J{ .m: R -> R }
Q:J{}
User:{ #:D->D:Q,K{} }
"""));}
@Test void reAbstractedThenReImplementedInAnotherBranch(){ok(List.of("""
R:{}
A:{ .m: R -> R }
X:A{ .m: R; }
Z:A{ .m: R -> R }
User:{ #:D->D:X,Z{} }
"""));}
@Test void reImplementedBelowReAbstraction(){ok(List.of("""
R:{}
A:{ .m: R -> R }
B:A{ .m: R; }
C:B{ .m: R -> R }
E:A{}
User:{ #:D->D:E,C{} }
"""));}
@Test void twoImplsReAbstractedTogetherBesideAThird(){ok(List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
X:A,B{ .m: R; }
C:{ .m: R -> R }
User:{ #:D->D:X,C{} }
"""));}
@Test void oneReAbstractedTwoLeftAmbiguous(){failWf("""
006| D:X,B,C{}
   | ^^^^^^^^^

While inspecting type declaration "D"
Ambiguous implementation for method ".m" with 0 parameters.
Implemented by the supertypes:
- "B"
- "C"
Type declaration "D" must declare a method ".m" explicitly implementing the desired behaviour.
""", List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
C:{ .m: R -> R }
X:A{ .m: R; }
D:X,B,C{}
"""));}
@Test void reAbstractedOnlyInAnUnrelatedBranch(){failWf("""
006| D:X,B{}
   | ^^^^^^^

While inspecting type declaration "D"
Ambiguous implementation for method ".m" with 0 parameters.
Implemented by the supertypes:
- "A"
- "B"
Type declaration "D" must declare a method ".m" explicitly implementing the desired behaviour.
""", List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
Y:{ .m: R; }
X:A,Y{}
D:X,B{}
"""));}
@Test void ambiguityResolvedByOwnMethod(){ok(List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
X:A{}
User:{ #:D->D:X,B{ .m->R } }
"""));}
@Test void reAbstractedOtherCapabilityKeepsImpl(){ok(List.of("""
R:{}
A:{ imm .m: R -> R; mut .m: R -> R }
X:A{ mut .m: R; }
B:{ mut .m: R -> R }
User:{ #:mut D->D:X,B{} }
"""));}
@Test void reAbstractedMethodInNestedDeclaration(){fail("""
003| User:{ #:C->C:A,B{} }
   |        -----^^^^^^^

While inspecting object literal "C" > method "User#" (line 3)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "B".
Hint: add an implementation for ".m" inside the object literal.
""", List.of("""
A:{ .m:A->this }
B:A{ .m:A }
User:{ #:C->C:A,B{} }
"""));}
@Test void reAbstractedMethodInNestedDeclarationOnlySubSuper(){fail("""
003| User:{ #:C->C:B{} }
   |        -----^^^^^

While inspecting object literal "C" > method "User#" (line 3)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "B".
Hint: add an implementation for ".m" inside the object literal.
""", List.of("""
A:{ .m:A->this }
B:A{ .m:A }
User:{ #:C->C:B{} }
"""));}
@Test void reAbstractedMethodImplementedInNestedDeclaration(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
User:{ #:C->C:A,B{ .m->A } }
"""));}
@Test void reAbstractedMethodListingOnlySubSuper(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
C:B{}
"""));}
@Test void overrideRefinesMutResultKeepingCapability(){ok(List.of("""
P:{}
Q:P{}
Sup:{ mut .h: mut P }
Sub:Sup{ mut .h: mut Q }
"""));}
@Test void overrideWeakensParamKeepingCapability(){ok(List.of("""
P:{}
Q:P{}
Sup:{ .g(x: mut Q): P }
Sub:Sup{ .g(x: mut P): P }
"""));}
@Test void overrideSpellsRedundantCapabilityOnTypeVariable(){ok(List.of("""
Sup[X:mut]:{ .h(x: X): X }
Sub[X:mut]:Sup[X]{ .h(x: mut X): mut X }
"""));}
@Test void overrideSpellsRedundantReadImmOnTypeVariable(){ok(List.of("""
Sup[X:imm]:{ .h(x: X): X }
Sub[X:imm]:Sup[X]{ .h(x: read/imm X): read/imm X }
"""));}
@Test void classGenericNarrowerBoundOverrideSpellsReadImm(){ok(List.of("""
Baz:{}
Sup[X:imm,mut]:{ .h(x: X): X }
Sub[Y:imm]:Sup[Y]{ .h(x: read/imm Y): read/imm Y -> x }
User:{ .viaSup(s: Sup[Baz]): Baz -> s.h(Baz); .use: Baz -> this.viaSup(Sub[Baz]) }
"""));}
@Test void overrideStrengthensResultCapability(){fail("""
003| Sub:Sup{ mut .h: iso P }
   | ---------^^^^^^^^^^^^^--

While inspecting type declaration "Sub"
Invalid method signature for "mut Sub.h".
The method ".h" returns type "iso P".
But "mut Sup.h" returns type "mut P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
P:{}
Sup:{ mut .h: mut P }
Sub:Sup{ mut .h: iso P }
"""));}
@Test void overrideWeakensParamCapability(){fail("""
003| Sub:Sup{ .g(x: read P): P }
   | ---------^^^^^^^^^^^^^^^^--

While inspecting type declaration "Sub"
Invalid method signature for "Sub.g(_)".
The method ".g(_)" accepts parameter 1 of type "read P".
But "Sup.g(_)" requires "mut P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
P:{}
Sup:{ .g(x: mut P): P }
Sub:Sup{ .g(x: read P): P }
"""));}
@Test void overrideChangesHygienicParamCapability(){fail("""
003| Sub:Sup{ .g(x: readH P): P }
   | ---------^^^^^^^^^^^^^^^^^--

While inspecting type declaration "Sub"
Invalid method signature for "Sub.g(_)".
The method ".g(_)" accepts parameter 1 of type "readH P".
But "Sup.g(_)" requires "mutH P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
P:{}
Sup:{ .g(x: mutH P): P }
Sub:Sup{ .g(x: readH P): P }
"""));}
@Test void overrideDropsReadImmOnTypeVariable(){fail("""
002| Sub[X:*]:Sup[X]{ .h(x: X): X }
   | -----------------^^^^^^^^^^^--

While inspecting type declaration "Sub[_]"
Invalid method signature for "Sub[_].h(_)".
The method ".h(_)" returns type "X".
But "Sup[_].h(_)" returns type "read/imm X".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
Sup[X:*]:{ .h(x: X): read/imm X }
Sub[X:*]:Sup[X]{ .h(x: X): X }
"""));}
@Test void overrideInLiteralStrengthensResultCapability(){fail("""
003| User:{ #: mut Sup -> mut Sup{ mut .h: iso P -> P } }
   |        --------------~~~~~~~~~^^^^^^^^^^^^^^^^^^~~

While inspecting object literal instance of "Sup" > method "User#" (line 3)
Invalid method signature for "mut Sup.h".
The method ".h" returns type "iso P".
But "mut Sup.h" returns type "mut P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
P:{}
Sup:{ mut .h: mut P }
User:{ #: mut Sup -> mut Sup{ mut .h: iso P -> P } }
"""));}
@Test void genericTwiceDifferingInCapabilityUnused(){ok(List.of("""
Bar:{}
Beer:{}
Foo[T:*]:{}
A:Foo[imm Bar],Foo[mut Beer]{}
"""));}
@Test void genericTwiceDifferingInNominalTypeRefinedToCommonSubtype(){ok(List.of("""
Bar:{}
Beer:{}
Both:Bar,Beer{}
Foo[T:*]:{ .get: T }
A:Foo[Bar],Foo[Beer]{ .get: Both -> Both }
"""));}
@Test void genericTwiceDifferingInCapabilityCanNotBeOverridden(){fail("""
005| A:Foo[imm Bar],Foo[mut Beer]{ .get: Both -> Both }
   | ------------------------------^^^^^^^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.get".
The method ".get" returns type "imm Both".
But "Foo[_].get" returns type "mut Beer".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
Bar:{}
Beer:{}
Both:Bar,Beer{}
Foo[T:*]:{ .get: T }
A:Foo[imm Bar],Foo[mut Beer]{ .get: Both -> Both }
"""));}
@Test void genericTwiceDifferingInCapabilityInherited(){failWf("""
004| A:Foo[imm Bar],Foo[mut Beer]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Supertypes disagree on the return type of method "imm .get" with 0 parameters.
Candidates:
- "imm Bar"
- "mut Beer"
The candidates differ in reference capability, and an overriding method must keep the reference capability, so no method ".get" can implement all the candidates.
""", List.of("""
Bar:{}
Beer:{}
Foo[T:*]:{ .get: T }
A:Foo[imm Bar],Foo[mut Beer]{}
"""));}
@Test void overrideDropsImmOnTypeVariable(){fail("""
002| Sub[X:*]:Sup[X]{ .h(x: X): X }
   | -----------------^^^^^^^^^^^--

While inspecting type declaration "Sub[_]"
Invalid method signature for "Sub[_].h(_)".
The method ".h(_)" returns type "X".
But "Sup[_].h(_)" returns type "imm X".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
Sup[X:*]:{ .h(x: X): imm X }
Sub[X:*]:Sup[X]{ .h(x: X): X }
"""));}
@Test void genericTwiceDifferingInCapabilityViaInexactBound(){failWf("""
002| A[Y:imm,mut]:Foo[Y],Foo[imm Y]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Supertypes disagree on the return type of method "imm .get" with 0 parameters.
Candidates:
- "Y"
- "imm Y"
The candidates differ in reference capability, and an overriding method must keep the reference capability, so no method ".get" can implement all the candidates.
""", List.of("""
Foo[T:*]:{ .get: T }
A[Y:imm,mut]:Foo[Y],Foo[imm Y]{}
"""));}
@Test void methodGenericSameCapabilityViaExactBoundInherited(){ok(List.of("""
Baz:{}
Foo:{ .get[T:mut]: T }
Bar:{ .get[T:mut]: mut T }
A:Foo,Bar{}
User:{ #(a: A): mut Baz -> a.get[mut Baz] }
"""));}
@Test void methodGenericSameReadImmViaExactBoundInherited(){ok(List.of("""
Baz:{}
Foo:{ .get[T:imm]: T }
Bar:{ .get[T:imm]: read/imm T }
A:Foo,Bar{}
User:{ #(a: A): Baz -> a.get[Baz] }
"""));}
@Test void classGenericSameReadImmViaExactBoundInherited(){ok(List.of("""
Foo[X:imm]:{ .get: X }
Bar[X:imm]:{ .get: read/imm X }
A[Y:imm]:Foo[Y],Bar[Y]{}
"""));}
@Test void classGenericAgainstNominalWithTheSameCapabilityInherited(){failWf("""
003| A[Y:imm]:Foo[Y],Foo[Bar]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Supertypes disagree on the return type of method "imm .get" with 0 parameters.
Candidates:
- "Y"
- "Bar"
The candidates are different types and "Y" is a generic type parameter, so no method ".get" can implement all the candidates.
""", List.of("""
Bar:{}
Foo[T:*]:{ .get: T }
A[Y:imm]:Foo[Y],Foo[Bar]{}
"""));}
@Test void classGenericAgainstNominalWithADifferentCapabilityInherited(){failWf("""
003| A[Y:imm,mut]:Foo[Y],Foo[Bar]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Supertypes disagree on the return type of method "imm .get" with 0 parameters.
Candidates:
- "Y"
- "imm Bar"
The candidates differ in reference capability, and an overriding method must keep the reference capability, so no method ".get" can implement all the candidates.
""", List.of("""
Bar:{}
Foo[T:*]:{ .get: T }
A[Y:imm,mut]:Foo[Y],Foo[Bar]{}
"""));}
@Test void classGenericNarrowerBoundSameReadImmInherited(){ok(List.of("""
Baz:{}
Foo[X:imm,mut]:{ .get: X }
Bar[X:imm,mut]:{ .get: read/imm X }
A[Y:imm]:Foo[Y],Bar[Y]{}
Make:{ #[Y:imm](y: Y): A[Y] -> { .get -> y } }
User:{
  .viaA[Z:imm](a: A[Z]): Z -> a.get;
  .asFoo[Z:imm](a: A[Z]): Foo[Z] -> a;
  .asBar[Z:imm](a: A[Z]): Bar[Z] -> a;
  .viaFoo(a: A[Baz]): Baz -> this.asFoo(a).get;
  .viaBar(a: A[Baz]): Baz -> this.asBar(a).get;
  .use: Baz -> this.viaBar(Make#Baz);
}
"""));}
@Test void classGenericNarrowerBoundSupertypeImpliedWithRedundantRc(){ok(List.of("""
Baz:{}
Foo[T:*]:{ .get: T }
Bar[X:imm,mut]:Foo[imm X]{}
A[Y:imm]:Foo[Y],Bar[Y]{}
User:{ .asFoo(a: A[Baz]): Foo[Baz] -> a; .get(a: A[Baz]): Baz -> a.get; .make: A[Baz] -> { .get -> Baz } }
"""));}
@Test void classGenericSameBoundDifferingReadImmInherited(){failWf("""
003| A[Y:imm,mut]:Foo[Y],Bar[Y]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Supertypes disagree on the return type of method "imm .get" with 0 parameters.
Candidates:
- "Y"
- "read/imm Y"
The candidates differ in reference capability, and an overriding method must keep the reference capability, so no method ".get" can implement all the candidates.
""", List.of("""
Foo[X:imm,mut]:{ .get: X }
Bar[X:imm,mut]:{ .get: read/imm X }
A[Y:imm,mut]:Foo[Y],Bar[Y]{}
"""));}
@Test void methodGenericSameReadViaExactBoundInherited(){ok(List.of("""
Baz:{}
Foo:{ .get[T:mut](t: read T): Baz }
Bar:{ .get[T:mut](t: read/imm T): Baz }
A:Foo,Bar{}
"""));}
@Test void methodGenericDifferingReadImmViaExactBoundInherited(){failWf("""
003| A:Foo,Bar{}
   | ^^^^^^^^^^^

While inspecting type declaration "A"
Supertypes disagree on the return type of method "imm .get" with 0 parameters.
Candidates:
- "T"
- "read/imm T"
The candidates differ in reference capability, and an overriding method must keep the reference capability, so no method ".get" can implement all the candidates.
""", List.of("""
Foo:{ .get[T:mut]: T }
Bar:{ .get[T:mut]: read/imm T }
A:Foo,Bar{}
"""));}
@Test void methodGenericSameCapabilityViaExactBoundOverridden(){ok(List.of("""
Foo:{ .get[T:mut]: T }
Bar:{ .get[T:mut]: mut T }
A:Foo,Bar{ .get[T:mut]: T }
"""));}
@Test void methodGenericSameCapabilityViaExactBoundArgument(){ok(List.of("""
Baz:{}
Foo:{ .set[T:read](t: T): Baz }
Bar:{ .set[T:read](t: read T): Baz }
A:Foo,Bar{}
"""));}
@Test void methodGenericSameCapabilityViaExactBoundNested(){ok(List.of("""
Box[T:*]:{}
Foo:{ .get[T:mut]: Box[T] }
Bar:{ .get[T:mut]: Box[mut T] }
A:Foo,Bar{}
"""));}
@Test void overrideBoundsAreComparedByPositionNotByName(){failWf("""
002| C:A{.m[Y:imm,X:imm](x:Y,y:X):Y->x}
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "C"
Invalid method signature for "C.m(_,_)".
The method ".m(_,_)" declares different capability bounds than the supertypes for generic type parameter 2.
Local declaration: "X:imm".
Capability bounds in the supertypes: "mut".
Generic type parameter names may differ from the supertypes; only the position matters.
""", List.of("""
A:{.m[X:imm,Y:mut](x:X,y:Y):X}
C:A{.m[Y:imm,X:imm](x:Y,y:X):Y->x}
"""));}
@Test void supertypesDisagreeOnBoundsInsideAGenericMethod(){failWf("""
003| A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
   |                         ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the capability bounds of generic type parameter 1 of method ".id(_)" with 1 parameter.
Generic type parameter names may differ across supertypes; only the position matters.
Candidates:
- "imm"
- "read"
Object literal "Both" cannot implement all of those supertypes.
""", List.of("""
Sup1:{ .id[X:imm](x:X):X }
Sup2:{ .id[X:read](x:X):X }
A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
"""));}
@Test void supertypesDisagreeOnTheReturnTypeInsideAGenericMethod(){failWf("""
003| A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
   |                         ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the return type of method "imm .get" with 0 parameters.
Candidates:
- "_AX"
- "Sup1"
Generic type parameter "X" of "Sup1.get" is named "_AX" here.
The candidates are different types and "_AX" is a generic type parameter, so no method ".get" can implement all the candidates.
""", List.of("""
Sup1:{ .get[X]:X }
Sup2:{ .get[X]:Sup1 }
A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
"""));}
@Test void supertypesDisagreeOnGenericArityInsideAGenericMethod(){failWf("""
003| A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
   |                         ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the number of generic type parameters of method ".id(_)" with 1 parameter.
Candidates:
- "[_AX:imm]"
- "[]"
Generic type parameter "X" of "Sup1.id(_)" is named "_AX" here.
Object literal "Both" cannot implement all of those supertypes.
""", List.of("""
Sup1:{ .id[X:imm](x:Sup1):Sup1 }
Sup2:{ .id(x:Sup1):Sup1 }
A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
"""));}
@Test void anAbstractMethodWithoutReturnTypeAndNoSupertype(){failWf("""
001| A:{ .m; }
   | ----^^---

While inspecting type declaration "A"
Missing return type for method ".m".
Add an explicit return type at the end of the signature.
Cannot infer signature of method ".m".
No supertype has a method named ".m" with 0 parameters.
""", List.of("""
A:{ .m; }
"""));}
@Test void anAbstractMethodWithAParameterWithoutReturnTypeAndNoSupertype(){failWf("""
001| A:{ .use(x: A); }
   | ----^^^^^^^^^^---

While inspecting type declaration "A"
Missing return type for method ".use(_)".
Add an explicit return type at the end of the signature.
Cannot infer signature of method ".use(_)".
No supertype has a method named ".use(_)" with 1 parameter.
""", List.of("""
A:{ .use(x: A); }
"""));}
@Test void anImmMethodDoesNotInheritFromAMutMethod(){failWf("""
002| B:A{ imm .m -> this }
   | -----^^^^^^^^^^^^^^--

While inspecting type declaration "B"
Missing return type for method "imm .m".
Cannot infer signature of method "imm .m".
No supertype has a method named "imm .m" with 0 parameters.
Did you mean "mut .m" ?
""", List.of("""
A:{ mut .m: A }
B:A{ imm .m -> this }
"""));}
@Test void aMethodWithTheWrongNumberOfParametersSuggestsTheMethodOfTheSupertype(){failWf("""
004| U:{ .u: A -> O.match{ .some -> A; .empty -> A } }
   |                     --^^^^^^^^^^---------------

While inspecting object literal instance of "OM[_]"
Missing return type for method ".some".
Cannot infer signature of method ".some".
No supertype has a method named ".some" with 0 parameters.
Did you mean ".some(_)" ?
Other methods of the supertypes:
- ".empty"
""", List.of("""
A:{}
OM[R]:{ .some(a: A): R; .empty: R }
O:{ .match[R](m: OM[R]): R -> m.empty }
U:{ .u: A -> O.match{ .some -> A; .empty -> A } }
"""));}
@Test void aMisspelledMethodSuggestsTheMethodOfTheSupertype(){failWf("""
004| U:{ .u: A -> B.if{ .then -> A; .els -> A } }
   |                  --------------^^^^^^^^^--

While inspecting object literal instance of "IfM[_]"
Missing return type for method ".els".
Cannot infer signature of method ".els".
No supertype has a method named ".els" with 0 parameters.
Did you mean ".else" ?
Other methods of the supertypes:
- ".then"
""", List.of("""
A:{}
IfM[R]:{ .then: R; .else: R }
B:{ .if[R](m: IfM[R]): R -> m.then }
U:{ .u: A -> B.if{ .then -> A; .els -> A } }
"""));}
@Test void aMisspelledMethodSuggestsEachMethodOfTheSupertypeWithThatName(){failWf("""
004| U:{ .u: A -> B.if{ .then -> A; .els -> A } }
   |                  --------------^^^^^^^^^--

While inspecting object literal instance of "IfM[_]"
Missing return type for method ".els".
Cannot infer signature of method ".els".
No supertype has a method named ".els" with 0 parameters.
Did you mean one of the following?
- ".else(_)"
- "read .else"
Other methods of the supertypes:
- ".then"
""", List.of("""
A:{}
IfM[R]:{ .then: R; .else(r: R): R; read .else: R }
B:{ .if[R](m: IfM[R]): R -> m.then }
U:{ .u: A -> B.if{ .then -> A; .els -> A } }
"""));}
@Test void aMethodNameWithoutTheDotIsReadAsAParameterName(){failWf("""
003| West:Direction{ turn -> North }
   | ----------------^^^^^^^^^^^^^--

While inspecting type declaration "West"
Cannot infer signature and name for a method with 1 parameter.
No supertype of type declaration "West" has a method with 1 parameter.
"turn" is read as a parameter name: a method name starts with ".", as in ".turn".
""", List.of("""
Direction:{ .turn: Direction }
North:Direction{ .turn -> North }
West:Direction{ turn -> North }
"""));}
@Test void aMethodNameWithoutTheDotListsTheOtherMethodsOfTheSupertypes(){failWf("""
003| West:Direction{ turn -> North }
   | ----------------^^^^^^^^^^^^^--

While inspecting type declaration "West"
Cannot infer signature and name for a method with 1 parameter.
No supertype of type declaration "West" has a method with 1 parameter.
"turn" is read as a parameter name: a method name starts with ".", as in ".turn".
Other methods of the supertypes:
- ".back"
""", List.of("""
Direction:{ .turn: Direction; .back: Direction }
North:Direction{ .turn -> North; .back -> North }
West:Direction{ turn -> North }
"""));}
@Test void aLambdaWithTooManyParametersListsTheMethodsOfTheSupertype(){failWf("""
003| U:{ .u(f: F[A,A]): A -> A; .k: A -> this.u{ a, b -> a } }
   |                                           --^^^^^^^^^--

While inspecting object literal instance of "F[_,_]"
Cannot infer signature and name for a method with 2 parameters.
No supertype of object literal instance of "F[_,_]" has a method with 2 parameters.
Methods of the supertypes:
- "#(_)"
""", List.of("""
A:{}
F[X,R]:{ #(x: X): R }
U:{ .u(f: F[A,A]): A -> A; .k: A -> this.u{ a, b -> a } }
"""));}
@Test void aMethodWithInferredNameWhoseSupertypeMethodIsTakenSaysSo(){failWf("""
002| B:A{ .m(a) -> this; a -> this }
   | --------------------^^^^^^^^^--

While inspecting type declaration "B"
Cannot infer signature and name for a method with 1 parameter.
Each method with 1 parameter of the supertypes is already implemented by another method of type declaration "B".
Methods of the supertypes:
- ".m(_)"
""", List.of("""
A:{ .m(a: A): A }
B:A{ .m(a) -> this; a -> this }
"""));}
}
