package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public final class GenericBoundsTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }
  static void failWf(String expected, List<String> input){
    typeFailRaw("In file: [###].fear\n\n"+expected+"Error 7 WellFormedness", input);
  }
  static void failParse(String expected, List<String> input){
    typeFailRaw("In file: [###].fear\n\n"+expected+"Error 2 UnexpectedToken", input);
  }
  static final String box= """
Box:{ #[T:*](t: T): mut Box[T] -> { .get -> t; .rget -> t; .riget -> t } }
Box[T:*]:{ mut .get: T; read .rget: read T; read .riget: read/imm T }
""";
  static final String people= """
Str:{} Bob:Str{}
Nat:{} TwentyFour:Nat{}
""";

@Test void subTypingCall(){ok(List.of("""
A:{ .m1(a: A): A -> a }
B:A{}
C:{ .m2: A -> A.m1(B) }
"""));}
@Test void genericReturnImplementedByAConcreteType(){ok(List.of("""
FortyTwo:{} FortyThree:{}
A[N:*]:{ .count: N; .sum: N }
B:A[FortyTwo]{ .count -> FortyTwo; .sum -> FortyTwo{} }
"""));}
@Test void genericReturnImplementedByTheWrongConcreteType(){fail("""
005| B:A[FortyTwo]{ .count -> FortyTwo; .sum -> FortyThree }
   |                                    --------^^^^^^^^^^

While inspecting object literal instance of "FortyThree" > method "B.sum" (line 5)
The body of method ".sum" of type declaration "B" is an expression returning "iso FortyThree".
Object literal is of type "iso FortyThree" instead of a subtype of "FortyTwo".
Method ".sum" inherited the signature from "A[FortyTwo].sum" as follows:
.sum: FortyTwo
""", List.of("""
Res1:{} Res2:{}
FortyTwo:{ .get: Res1 -> Res1 }
FortyThree:{ .get: Res2 -> Res2 }
A[N:*]:{ .count: N; .sum: N }
B:A[FortyTwo]{ .count -> FortyTwo; .sum -> FortyThree }
"""));}
@Test void genericReturnImplementedWithTheWrongCapability(){fail("""
004| B:A[FortyTwo]{ .count -> FortyTwo; .sum(n) -> n }
   |                                    -----------^

While inspecting parameter "n" > method "B.sum(_)" (line 4)
The body of method ".sum(_)" of type declaration "B" is an expression returning "mut FortyTwo".
Parameter "n" has type "mut FortyTwo" instead of a subtype of "imm FortyTwo".
Method ".sum(_)" inherited the signature from "A[FortyTwo].sum(_)" as follows:
mut .sum(n: mut FortyTwo): FortyTwo
""", List.of("""
Res1:{}
FortyTwo:{ .get: Res1 -> Res1 }
A[N:*]:{ mut .count: N; mut .sum(n: mut FortyTwo): N }
B:A[FortyTwo]{ .count -> FortyTwo; .sum(n) -> n }
"""));}
@Test void thisInsideANestedLiteralIsTheTopLevelThis(){ok(List.of("""
A:{ .a: C -> B{ this.c }.c; .c: C -> {} }
B:{ .c: C }
C:{}
"""));}
@Test void literalCapturesThis(){ok(List.of("""
Void:{}
Let:{ #[V:*,R:*](l: mut Let[V, R]): R -> l.in(l.var) }
Let[V:*,R:*]:{ mut .var: V; mut .in(v: V): R }
Ref[X:*]:{
  mut .swap(x: X): X;
  mut .set(x: X): Void -> Let#(mut Let[X,Void]{ .var -> this.swap(x); .in(_) -> Void });
  }
"""));}
@Test void boxWithTwoCapabilitiesForHash(){ok(List.of("""
Box:{ #[R:*](r: R): mut Box[R] -> { r } }
Box[R:*]:{ mut #: R; read #: read/imm R }
"""));}
@Test void boxWithStarStarBoundsOnTheType(){ok(List.of("""
Box:{ #[R:imm,mut](r: R): mut Box[R] -> {r} }
Box[R:**]:{ mut #: R }
"""));}
@Test void extraMethodInALiteral(){ok(List.of("""
A:{ .m1: A -> {'self
  .m1: A -> self.privateOne;
  .privateOne: A -> {};
  } }
"""));}
@Test void extraGenericMethodInALiteral(){ok(List.of("""
A:{ .m1: A -> {'self
  .m1: A -> self.privateOne[A];
  .privateOne[X:*]: A -> {};
  } }
"""));}
@Test void methodCalledOnAnInlineDeclaration(){ok(List.of("""
Foo:{} Bar:{}
A:{ .foo: Foo -> {} }
B:{ .bar: Bar -> {} }
Test2:{ #: Foo -> Anon2:A,B{}.foo }
Test1:{ #: Foo -> (Anon1:B,A{}).foo }
"""));}
@Test void inlineDeclarationImplementingTwoTypes(){ok(List.of("""
A:{ .foo: A }
B:{ .bar: B -> this }
Test:{ #: B -> Anon:A,B{'self .foo -> self } }
"""));}
@Test void genericPromotionToIsoIsNotSound(){fail("""
004| Bar:{ .k[Y:*](y: Y): iso Beer[Y] -> Foo.m[Y](y) }
   |       ------------------------------^^^^^^^^^^^

While inspecting method call ".m(_)" > method "Bar.k(_)" (line 4)
The body of method ".k(_)" of type declaration "Bar" is an expression returning "mut Beer[Y]".
Method call "Foo.m(_)" has type "mut Beer[Y]" instead of a subtype of "iso Beer[Y]".
""", List.of("""
Baz:{}
Beer[X:*]:{ mut .x: X; read .x: read X }
Foo:{ .m[X:*](x: X): mut Beer[X] -> {x} }
Bar:{ .k[Y:*](y: Y): iso Beer[Y] -> Foo.m[Y](y) }
Break:{
  .m1(y: mut Baz): Beer[mut Baz] -> Bar.k(y);
  .ohNo(y: mut Baz): imm Baz -> this.m1(y).x;
  }
"""));}
@Test void genericPromotionToImmIsNotSound(){fail("""
004| Bar:{ .k[Y:*](y: Y): imm Beer[Y] -> Foo.m[Y](y) }
   |       ------------------------------^^^^^^^^^^^

While inspecting method call ".m(_)" > method "Bar.k(_)" (line 4)
The body of method ".k(_)" of type declaration "Bar" is an expression returning "mut Beer[Y]".
Method call "Foo.m(_)" has type "mut Beer[Y]" instead of a subtype of "Beer[Y]".
""", List.of("""
Baz:{}
Beer[X:*]:{ mut .x: X; read .x: read X }
Foo:{ .m[X:*](x: X): mut Beer[X] -> {x} }
Bar:{ .k[Y:*](y: Y): imm Beer[Y] -> Foo.m[Y](y) }
Break:{
  .m1(y: mut Baz): Beer[mut Baz] -> Bar.k(y);
  .ohNo(y: mut Baz): imm Baz -> this.m1(y).x;
  }
"""));}
@Test void genericPromotionFromAnIsoParameter(){ok(List.of("""
Baz:{}
Beer[X:*]:{ mut .x: X; read .x: read X }
Foo:{ .m[X:*](x: X): mut Beer[X] -> {x} }
Bar:{ .k[Y:*](y: iso Y): iso Beer[Y] -> Foo.m[Y](y) }
Break:{
  .m1(y: iso Baz): Beer[mut Baz] -> Bar.k[mut Baz](y);
  .ohNo(y: iso Baz): imm Baz -> this.m1(y).x;
  }
"""));}
@Test void literalImplementingAGenericMethodOfItsOwnType(){ok(List.of("""
Test:{ .foo[Y:*](x: Y): Test -> Test{ .foo(hello) -> Test } }
"""));}
@Test void covariantOverrideAcrossAFactory(){ok(List.of("""
Colour:{} Num:{} Five:Num{}
FPoint:{ #(x: Num, y: Num): Point -> { .x -> x; .y -> y } }
Point:{
  .x: Num;
  .y: Num;
  .withX(x: Num): Point -> FPoint#(x, this.y);
  .withY(y: Num): Point -> FPoint#(this.x, y);
  }
ColourPoint:Point{
  .colour: Colour;
  .withX(x: Num): ColourPoint -> FColourPoint#(x, this.y, this.colour);
  .withY(y: Num): ColourPoint -> FColourPoint#(this.x, y, this.colour);
  }
FColourPoint:{ #(x: Num, y: Num, colour: Colour): ColourPoint -> {
  .x -> x; .y -> y; .colour -> colour;
  }}
Usage:{ #(cp: ColourPoint): ColourPoint -> cp.withX(Five) }
"""));}
@Test void branchingReturnTypes(){ok(List.of("""
Opts:{ #[T:*](x: T): mut Opt[T] -> { .match(m) -> m.some(x) } }
Opt[T:*]:{
  mut  .match[R:*](m: mut OptMatch[T, R]): R -> m.empty;
  read .match[R:*](m: mut OptMatch[read T, R]): R -> m.empty;
  imm  .match[R:*](m: mut OptMatch[imm T, R]): R -> m.empty;
  }
OptMatch[T:*,R:*]:{ mut .some(x: T): R; mut .empty: R }
N:{} Zero:N{}
Test:{ .test(opt: Opt[N]): N -> opt.match{
  .some(n) -> n;
  .empty -> Zero;
  }}
"""));}
@Test void genericMethodOnALiteral(){ok(List.of("""
V:{}
M:{ .m[X:*](x:X):X }
MV:{ .mv(v:V): V -> M{x->x}.m[V](v) }
"""));}
@Test void foldWithAnExplicitlyTypedFunction(){ok(List.of("""
Num:{ +(other: Num): Num }
Zero:Num{ +(other) -> other }
List[E:*]:{ .fold[S:*](acc: S, f: Fold[S, E]): S -> Abort! }
Fold[S:*,T:*]:{ #(acc: S, x: T): S }
Abort:{ ![R:**]: R -> this! }
Break:{ #(l: List[Num]): Num -> l.fold[Num](Zero, Fold[Num, Num]{acc, n -> acc + n}) }
"""));}
@Test void foldWithAnInferredFunction(){ok(List.of("""
Num:{ +(other: Num): Num }
Zero:Num{ +(other) -> other }
List[E:*]:{ .fold[S:*](acc: S, f: Fold[S, E]): S -> Abort! }
Fold[S:*,T:*]:{ #(acc: S, x: T): S }
Abort:{ ![R:**]: R -> this! }
Break:{ #(l: List[Num]): Num -> l.fold[Num](Zero, {acc, n -> acc + n}) }
"""));}
@Test void foldInfersTheAccumulatorFromAnInferredFunction(){ok(List.of("""
Num:{ +(other: Num): Num }
Zero:Num{ +(other) -> other }
List[E:*]:{ .fold[S:*](acc: S, f: Fold[S, E]): S -> Abort! }
Fold[S:*,T:*]:{ #(acc: S, x: T): S }
Abort:{ ![R:**]: R -> this! }
Break:{ #(l: List[Num]): Num -> l.fold(Zero, {acc, n -> acc + n}) }
"""));}
@Test void foldInfersTheAccumulatorFromAFunctionParameter(){ok(List.of("""
Num:{ +(other: Num): Num }
Zero:Num{ +(other) -> other }
List[E:*]:{ .fold[S:*](acc: S, f: Fold[S, E]): S -> Abort! }
Fold[S:*,T:*]:{ #(acc: S, x: T): S }
Abort:{ ![R:**]: R -> this! }
Break:{ #(l: List[Num], f: Fold[Num, Num]): Num -> l.fold(Zero, f) }
"""));}
@Test void foldInfersTheAccumulatorFromAFunctionParameterWithoutExpectedType(){ok(List.of("""
Num:{ +(other: Num): Num }
Zero:Num{ +(other) -> other }
List[E:*]:{ .fold[S:*](acc: S, f: Fold[S, E]): S -> Abort! }
Fold[S:*,T:*]:{ #(acc: S, x: T): S }
Abort:{ ![R:**]: R -> this! }
Break:{ #(l: List[Num], f: Fold[Num, Num]): Num -> l.fold(Zero, f) + Zero }
"""));}
@Test void partiallyAppliedGenericSuperType(){ok(List.of("""
Default:{} Foo:{}
A[X:*,Y:*]:{}
B[X:*]:A[X,Default]{}
Break:{ #(b: B[Foo]): A[Foo,Default] -> b }
"""));}
@Test void literalCannotImplementATypeVariable(){failWf("""
001| A[X:*]:{ #: X -> {} }
   |                  ^^

While inspecting object literal "{...}"
Object literal "{...}" cannot implement "X".
"X" is a generic type parameter; object literals can only implement nominal types.
""", List.of("""
A[X:*]:{ #: X -> {} }
"""));}
@Test void literalWithMethodCannotImplementATypeVariable(){failWf("""
001| A[X:*]:{ #: X -> {this} }
   |                  ^^^^^^

While inspecting object literal "{...}"
Object literal "{...}" cannot implement "X".
"X" is a generic type parameter; object literals can only implement nominal types.
""", List.of("""
A[X:*]:{ #: X -> {this} }
"""));}
@Test void literalCannotImplementAMutTypeVariable(){failWf("""
001| A[X:*]:{ #: mut X -> {} }
   |                      ^^

While inspecting object literal "{...}"
Object literal "{...}" cannot implement "mut X".
"X" is a generic type parameter; object literals can only implement nominal types.
""", List.of("""
A[X:*]:{ #: mut X -> {} }
"""));}
@Test void literalCannotImplementAReadImmTypeVariable(){failWf("""
001| A[X:*]:{ read #: read/imm X -> {} }
   |                                ^^

While inspecting object literal "{...}"
Object literal "{...}" cannot implement "read/imm X".
"X" is a generic type parameter; object literals can only implement nominal types.
""", List.of("""
A[X:*]:{ read #: read/imm X -> {} }
"""));}
@Test void literalCannotImplementARenamedTypeVariable(){failWf("""
002| B[X:*]:Sup{ .m -> {} }
   |                   ^^

While inspecting object literal "{...}"
Object literal "{...}" cannot implement "_AX".
"_AX" is a generic type parameter; object literals can only implement nominal types.
Generic type parameter "X" of "Sup.m" is named "_AX" here.
""", List.of("""
Sup:{ .m[X:*]: X; }
B[X:*]:Sup{ .m -> {} }
"""));}
@Test void nestedLiteralCannotImplementARenamedTypeVariable(){failWf("""
003| B[X:*]:Sup{ .m -> { .k -> {} } }
   |                           ^^

While inspecting object literal "{...}"
Object literal "{...}" cannot implement "_AX".
"_AX" is a generic type parameter; object literals can only implement nominal types.
Generic type parameter "X" of "Sup.m" is named "_AX" here.
""", List.of("""
Sup:{ .m[X:*]: K[X]; }
K[Y:*]:{ .k: Y; }
B[X:*]:Sup{ .m -> { .k -> {} } }
"""));}
@Test void literalCannotImplementATypeVariableRenamedFromARedeclaration(){failWf("""
003| B[Y:*]:Mid{ .m -> {} }
   |                   ^^

While inspecting object literal "{...}"
Object literal "{...}" cannot implement "_AY".
"_AY" is a generic type parameter; object literals can only implement nominal types.
Generic type parameter "Y" of "Mid.m" is named "_AY" here.
""", List.of("""
Top:{ .m[X:*]: X; }
Mid:Top{ .m[Y:*]: Y; }
B[Y:*]:Mid{ .m -> {} }
"""));}
@Test void literalMethodNotInferredAsReceiver(){failWf("""
001| A[X:*]:{ #: X -> {this}* }
   |                  -^^^^-

While inspecting object literal "{...}"
Cannot infer signature and name for a method with 0 parameters.
No supertype of object literal "{...}" has a method with 0 parameters.
""", List.of("""
A[X:*]:{ #: X -> {this}* }
"""));}
@Test void uninferredLiteralInGenericDeclaration(){failWf("""
004| B[R5:*]: { mut .loop(f: mut Flow[R5]): mut B[R5] -> f.match{ .return(rv) -> Any#; }**; }
   |                                                            ^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "Match[_,_]"
Type inference concluded that this object literal implements "Match[R5,?]",
but it could not infer generic type argument 2 for generic type parameter "R" of "Match[_,_]".
""", List.of("""
Any:{#[T:*]:T->Any#}
Flow[T:*]: { mut .match[R:*](m: mut Match[T,R]): R }
Match[T:*,R:*]: { mut .return(t: T): R; }
B[R5:*]: { mut .loop(f: mut Flow[R5]): mut B[R5] -> f.match{ .return(rv) -> Any#; }**; }
"""));}
@Test void uninferredLiteralHeadPrintsEachKnownTypeArgumentOnce(){failWf("""
004| B[R5:*,R6:*]: { mut .loop(f: mut Flow[R5,R6]): mut B[R5,R6] -> f.match{ .return(rv, uv) -> Any#; }**; }
   |                                                                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "Match[_,_,_]"
Type inference concluded that this object literal implements "Match[R5,R6,?]",
but it could not infer generic type argument 3 for generic type parameter "R" of "Match[_,_,_]".
""", List.of("""
Any:{#[T:*]:T->Any#}
Flow[T:*,U:*]: { mut .match[R:*](m: mut Match[T,U,R]): R }
Match[T:*,U:*,R:*]: { mut .return(t: T, u: U): R; }
B[R5:*,R6:*]: { mut .loop(f: mut Flow[R5,R6]): mut B[R5,R6] -> f.match{ .return(rv, uv) -> Any#; }**; }
"""));}
@Test void literalCannotBePassedAsATypeVariable(){failWf("""
001| A[X:*]:{ .m(x: X): X -> x; .k: X -> this.m({}) }
   |                                            ^^

While inspecting object literal "{...}"
Object literal "{...}" cannot implement "X".
"X" is a generic type parameter; object literals can only implement nominal types.
""", List.of("""
A[X:*]:{ .m(x: X): X -> x; .k: X -> this.m({}) }
"""));}
@Test void typeVariableCannotBeUsedAsALiteralName(){failParse("""
001| A[X:*]:{ #: X -> X }
   |        --~~~~~~~~^--

While inspecting method body > method declaration > type declaration body > type declaration > full file
Generic type parameter "X" is in scope here.
Name "X" is also used as a type name.
""", List.of("""
A[X:*]:{ #: X -> X }
"""));}
@Test void literalCopiesTheMethodsOfItsEnclosingType(){ok(List.of("""
V:{ #[X:*](x: X): X -> x }
A[E:*]:{
  mut  .get(v: V): E -> this.get(v);
  read .get(v: V): read/imm E -> this.get(v);
  mut .nest(e: E): mut A[E] -> {
    mut  .get(v: V): E -> v#e;
    read .get(v: V): read/imm E -> v#[read/imm E]e;
    };
  }
"""));}
@Test void sameGenericImplementedTwiceWithDifferentArguments(){ok(List.of("""
Void:{}
A[X:*]:{}
Foo:{} Bar:{}
B:A[Foo],A[Bar]{}
CallMe:{ .m1(a: A[Foo]): Void -> {}; .m2(a: A[Bar]): Void -> {} }
Caller:{ .m1: Void -> CallMe.m1(B); .m2: Void -> CallMe.m2(B) }
"""));}
@Test void namedInlineDeclarationWithACapability(){ok(List.of("""
List[T:*]:{} Bob:{}
Bar[X:*]:{ .m(x: X): mut Foo[X] -> mut Foo[X:*]:{ mut .get: X -> x } }
CanCall:{ #: Bob -> Bar[Bob].m(Bob).get }
"""));}
@Test void immThisAsImmInReadMethod(){ok(List.of("""
A:{ .m1: imm B -> B:{'self
  imm .foo: B -> self;
  read .bar: B -> self.foo;
  }}
"""));}
@Test void hygienicBoundsAllowIsoPromotionOfAnArgument(){ok(List.of("""
Foo:{}
A:{ #[X:mut,mutH,readH](x: X, f: mut Foo): mut Foo -> f }
Expect:{ .isoFoo(f: iso Foo): iso Foo -> f }
Good:{ #[Y:mutH,readH](y: Y, isoF: iso Foo): iso Foo -> Expect.isoFoo(A#[Y](y, isoF)) }
Concrete:{ #(y: mutH Foo, isoF: iso Foo): iso Foo -> Expect.isoFoo(A#[mutH Foo](y, isoF)) }
"""));}
@Test void nonHygienicBoundsBlockIsoPromotionOfAnArgument(){fail("""
004| Bad:{ #[Y:mut,mutH,readH](y: Y, isoF: iso Foo): iso Foo -> Expect.isoFoo(A#[Y](y, isoF)) }
   |       -----------------------------------------------------~~~~~~~~~~~~~~^^^^^^^^^^^^^^~

While inspecting method "Bad#(_,_)" (line 4)
This call to method "Expect.isoFoo(_)" cannot typecheck.
Argument 1 has type "mut Foo".
Method call "A#(_,_)" has type "mut Foo" instead of a subtype of "iso Foo".

Type required by each promotion:
- "iso Foo" (As declared, Strengthen result)
""", List.of("""
Foo:{}
A:{ #[X:mut,mutH,readH](x: X, f: mut Foo): mut Foo -> f }
Expect:{ .isoFoo(f: iso Foo): iso Foo -> f }
Bad:{ #[Y:mut,mutH,readH](y: Y, isoF: iso Foo): iso Foo -> Expect.isoFoo(A#[Y](y, isoF)) }
"""));}
@Test void invalidBoundsOnAnInlineDeclaration(){fail("""
002| Foo:{ .bar: A[mutH Foo] -> A[mutH Foo] }
   | ------------^^^^^^^^^^^-----------------

While inspecting type declaration "Foo"
The type "A[mutH Foo]" is invalid.
Generic type argument 1 ("mutH Foo") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capabilities "imm" or "mut".
""", List.of("""
A[X:imm,mut]:{}
Foo:{ .bar: A[mutH Foo] -> A[mutH Foo] }
"""));}
@Test void invalidTraitBoundsTopLevel(){fail("""
002| Break:A[imm Break]{}
   | ------^^^^^^^^^^^^--

While inspecting type declaration "Break"
The type "A[Break]" is invalid.
Generic type argument 1 ("imm Break") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capability "mut".
""", List.of("""
A[X:mut]:{}
Break:A[imm Break]{}
"""));}
@Test void invalidTraitBoundsTopLevelWithAbstractMethod(){fail("""
002| Break:A[imm Break]{}
   | ------^^^^^^^^^^^^--

While inspecting type declaration "Break"
The type "A[Break]" is invalid.
Generic type argument 1 ("imm Break") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capability "mut".
""", List.of("""
A[X:mut]:{ .a1: X }
Break:A[imm Break]{}
"""));}
@Test void validTraitBoundsTopLevel(){ok(List.of("""
A[X:mut]:{}
Break:A[mut Break]{}
"""));}
@Test void invalidTraitBoundsInline(){fail("""
003| BreakOuter:{ #: BreakInner -> BreakInner: A[imm Break]{} }
   |              -----------------~~~~~~~~~~~~^^^^^^^^^^^^~~

While inspecting object literal "BreakInner" > method "BreakOuter#" (line 3)
The type "A[Break]" is invalid.
Generic type argument 1 ("imm Break") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capability "mut".
""", List.of("""
A[X:mut]:{}
Break:{}
BreakOuter:{ #: BreakInner -> BreakInner: A[imm Break]{} }
"""));}
@Test void validTraitBoundsInline(){ok(List.of("""
A[X:mut]:{}
Break:{}
BreakOuter:{ #: BreakInner -> BreakInner: A[mut Break]{} }
"""));}
@Test void freshLiteralArgumentIsCreatedWithTheRequiredCapability(){ok(List.of("""
A:{ #[X:mut](x: X): X -> x }
Break:{ #: imm Break -> A#(imm Break) }
"""));}
@Test void inferredTypeArgumentKeepsATypeVariableOutsideTheBound(){fail("""
003| A:{ .f[Z:mut](z: Z): Foo -> Util.m(z) }
   |     ------------------------^^^^^^^^^

While inspecting method call ".m(_)" > method "A.f(_)" (line 3)
This call to method "Util.m(_)" cannot typecheck.
Generic type argument 1 ("Z") does not satisfy the bounds
for generic type parameter "Y" in "Util.m(_)".
Here "Y" can only use capability "imm".
But generic type argument "Z" can only use capability "mut".

See inferred typing context below for how type "Z" was introduced:
Util.m[imm,Z](z)
""", List.of("""
Foo:{}
Util:{ .m[Y:imm](y: Y): Foo -> Foo }
A:{ .f[Z:mut](z: Z): Foo -> Util.m(z) }
"""));}
@Test void inferredTypeArgumentRewritesATypeVariableWithTheSameBound(){ok(List.of("""
Foo:{}
Util:{ .m[Y:imm](y: Y): Foo -> Foo }
A:{ .f[Z:imm](z: Z): Foo -> Util.m(z) }
"""));}
@Test void inferredTypeArgumentKeepsAClassTypeVariableOutsideTheBound(){fail("""
003| A[Z:mut]:{ .f(z: Z): Foo -> Util.m(z) }
   |            -----------------^^^^^^^^^

While inspecting method call ".m(_)" > method "A[_].f(_)" (line 3)
This call to method "Util.m(_)" cannot typecheck.
Generic type argument 1 ("Z") does not satisfy the bounds
for generic type parameter "Y" in "Util.m(_)".
Here "Y" can only use capability "imm".
But generic type argument "Z" can only use capability "mut".

See inferred typing context below for how type "Z" was introduced:
Util.m[imm,Z](z)
""", List.of("""
Foo:{}
Util:{ .m[Y:imm](y: Y): Foo -> Foo }
A[Z:mut]:{ .f(z: Z): Foo -> Util.m(z) }
"""));}
@Test void literalTypeArgumentOutsideTheBoundIsAKindingError(){fail("""
[###]
The type "Foo[Y]" is invalid.
Generic type argument 1 ("Y") does not satisfy the bounds
for generic type parameter "X" in "Foo[_]".
Here "X" can only use capability "imm".
[###]""", List.of("""
Foo[X:imm]:{ .get: X }
A:{ .m[Y:imm,mut](y: imm Y): Foo[imm Y] -> Foo[Y]{ .get -> y } }
"""));}
@Test void immParameterCannotSatisfyAMutBound(){fail("""
003| Break:{ .m(f: imm Foo): imm Foo -> A#(f) }
   |         ---------------------------~~~^~

While inspecting method "Break.m(_)" (line 3)
This call to method "A#(_)" cannot typecheck.
Argument 1 has type "imm Foo".
Parameter "f" has type "imm Foo" instead of a subtype of "mut Foo".

Type required by each promotion:
- "mut Foo" (As declared)
- "iso Foo" (Strengthen result)

See inferred typing context below for how type "mut Foo" was introduced:
Break:{.m(f:Foo):Foo->A#[imm,mut Foo](f)}
""", List.of("""
Foo:{}
A:{ #[X:mut](x: X): X -> x }
Break:{ .m(f: imm Foo): imm Foo -> A#(f) }
"""));}
@Test void explicitTypeArgumentMustSatisfyTheMethodBound(){fail("""
003| Break:{ .m(f: imm Foo): imm Foo -> A#[imm Foo](f) }
   |         ---------------------------^^^^^^^^^^^^^^

While inspecting method call "#(_)" > method "Break.m(_)" (line 3)
This call to method "A#(_)" cannot typecheck.
Generic type argument 1 ("imm Foo") does not satisfy the bounds
for generic type parameter "X" in "A#(_)".
Here "X" can only use capability "mut".
""", List.of("""
Foo:{}
A:{ #[X:mut](x: X): X -> x }
Break:{ .m(f: imm Foo): imm Foo -> A#[imm Foo](f) }
"""));}
@Test void validTraitBoundsOnAMethodCall(){ok(List.of("""
A:{ #[X:mut](x: X): X -> x }
Break:{ #: mut Break -> A#(mut Break) }
"""));}
@Test void methodBoundsWiderThanTheTypeBounds(){fail("""
002| A:{ .bar[Y:mut,read,imm]: imm Foo[Y] -> imm Foo[Y] }
   | ------------------------------^^^^^^----------------

While inspecting type declaration "A"
The type "Foo[Y]" is invalid.
Generic type argument 1 ("Y") does not satisfy the bounds
for generic type parameter "X" in "Foo[_]".
Here "X" can only use capability "mut".
But generic type argument "Y" can only use capabilities "imm" or "mut" or "read".
""", List.of("""
Foo[X:mut]:{}
A:{ .bar[Y:mut,read,imm]: imm Foo[Y] -> imm Foo[Y] }
"""));}
@Test void methodBoundsNarrowerThanTheTypeBounds(){ok(List.of("""
Foo[X:mut,read]:{}
A:{ .bar[Y:mut]: imm Foo[Y] -> imm Foo[Y] }
"""));}
@Test void readImmSubsumption(){ok(List.of("""
Foo[X:read,imm]:{}
A:{ .bar[Y:mut,read,imm]: imm Foo[read/imm Y] -> imm Foo[read/imm Y] }
"""));}
@Test void isoPromotionOfABoxOfImm(){ok(List.of("""
A:{ #[S:imm](s: S): iso Box[S] -> Box#s }
""", box));}
@Test void isoPromotionOfABoxPassedToAnIsoParameter(){ok(List.of("""
B:{ #[Y:*](b: iso Y): mut B -> {} }
A:{ #[S:imm](s: S): mut B -> B#[mut Box[S]](Box#[S]s) }
""", box));}
@Test void personFactory(){ok(List.of("""
FPerson:{ #(name: Str, age: Nat): Person -> Person:{
  .name: Str -> name;
  .age: Nat -> age;
  }}
Ex:{
  .create: Person -> FPerson#(Bob, TwentyFour);
  .name(p: Person): Str -> p.name;
  }
""", people));}
@Test void genericPerson(){ok(List.of("""
Person[N:*]:{ .name: Str; .age: imm N }
FPerson:{ #[N:*](name: Str, age: imm N): Person[N] -> {
  .name: Str -> name;
  .age: imm N -> age;
  }}
Ex:{
  .create: Person[Nat] -> FPerson#[Nat](Bob, TwentyFour);
  .name(p: Person[Nat]): Str -> p.name;
  }
""", people));}
@Test void genericPersonInline(){ok(List.of("""
FPerson:{ #[N:*](name: Str, age: imm N): Person[N] -> Person[N:*]:{
  .name: Str -> name;
  .age: imm N -> age;
  }}
Ex:{
  .create: Person[Nat] -> FPerson#[Nat](Bob, TwentyFour);
  .name(p: Person[Nat]): Str -> p.name;
  }
""", people));}
@Test void inlineBoundsForwarding(){ok(List.of("""
FPerson:{ #[N:imm](name: Str, age: imm N): Person[N] -> Person[N:imm]:{
  .name: Str -> name;
  .age: imm N -> age;
  }}
Ex:{
  .create: Person[Nat] -> FPerson#[Nat](Bob, TwentyFour);
  .name(p: Person[Nat]): Str -> p.name;
  }
""", people));}
@Test void inlineBoundsForwardingMismatch(){ok(List.of("""
FPerson:{ #[N:imm](name: Str, age: imm N): Person[N] -> Person[N:*]:{
  .name: Str -> name;
  .age: imm N -> age;
  }}
Ex:{
  .create: Person[Nat] -> FPerson#(Bob, TwentyFour);
  .name(p: Person[Nat]): Str -> p.name;
  }
""", people));}
@Test void boundsForwardingImplicit(){ok(List.of("""
Person[N:imm]:{ .name: Str; .age: N }
FPerson:{ #[N:*](name: Str, age: imm N): Person[imm N] -> {
  .name -> name;
  .age -> age;
  }}
Ex:{
  .create: Person[Nat] -> FPerson#[Nat](Bob, TwentyFour);
  .name(p: Person[Nat]): Str -> p.name;
  }
""", people));}
@Test void boundsForwardingImplicitBreak(){fail("""
002| FPerson:{ #[N:*](name: Str, age: imm N): Person[N] -> {
   |                                          ^^^^^^^^^
   | ... 2 lines ...
005|   }}

While inspecting type declaration "FPerson"
The type "Person[N]" is invalid.
Generic type argument 1 ("N") does not satisfy the bounds
for generic type parameter "N" in "Person[_]".
Here "N" can only use capability "imm".
But generic type argument "N" can only use capabilities "imm" or "mut" or "read".
""", List.of("""
Person[N:imm]:{ .name: Str; .age: N }
FPerson:{ #[N:*](name: Str, age: imm N): Person[N] -> {
  .name -> name;
  .age -> age;
  }}
Ex:{
  .create: Person[Nat] -> FPerson#[Nat](Bob, TwentyFour);
  .name(p: Person[Nat]): Str -> p.name;
  }
""", people));}
@Test void boundsForwardingExplicit(){ok(List.of("""
Person[N:imm]:{ .name: Str; .age: N }
FPerson:{ #[N:*](name: Str, age: imm N): Person[imm N] -> Fresh[N:*]:Person[imm N]{
  .name -> name;
  .age -> age;
  }}
Break:{ #: Fresh[mut Nat] }
Ex:{
  .create: Person[Nat] -> FPerson#[Nat](Bob, TwentyFour);
  .name(p: Person[Nat]): Str -> p.name;
  }
""", people));}
@Test void boundsForwardingExplicitBreak(){fail("""
002| FPerson:{ #[N:*](name: Str, age: imm N): Person[imm N] -> Fresh[N:*]:Person[N]{
   |                                                                      ^^^^^^^^^
   | ... 2 lines ...
005|   }}

While inspecting object literal "Fresh[_]" > method "FPerson#(_,_)" (line 2)
The type "Person[N]" is invalid.
Generic type argument 1 ("N") does not satisfy the bounds
for generic type parameter "N" in "Person[_]".
Here "N" can only use capability "imm".
But generic type argument "N" can only use capabilities "imm" or "mut" or "read".
""", List.of("""
Person[N:imm]:{ .name: Str; .age: N }
FPerson:{ #[N:*](name: Str, age: imm N): Person[imm N] -> Fresh[N:*]:Person[N]{
  .name -> name;
  .age -> age;
  }}
Break:{ #: Fresh[mut Nat] }
Ex:{
  .create: Person[Nat] -> FPerson#[Nat](Bob, TwentyFour);
  .name(p: Person[Nat]): Str -> p.name;
  }
""", people));}
@Test void funnellingInADifferentOrder(){ok(List.of("""
Foo:{ .m[X:imm,Y:imm](x: X, y: Y): Box[X,Y] ->
  Anon[Y:imm, X:imm]: Box[X,Y]{.x -> x; .y -> y}
  }
Box[X:imm,Y:imm]:{ .x: X; .y: Y }
"""));}
@Test void funnellingCanOnlyUseGenericsInScope(){failWf("""
003|     .x -> x; .y -> y; .z: Z -> b.z}
   |                           ^

While inspecting a type name
Type "Z" is not declared in package "p" and is not made visible via "use".
In scope:
- "Box"
- "Foo"
""", List.of("""
Foo:{ .m[X:imm,Y:imm](x: X, y: Y): Box[X,Y] ->
  Box[X,Y]{'b
    .x -> x; .y -> y; .z: Z -> b.z}
  }
Box[X:imm,Y:imm]:{ .x: X; .y: Y }
"""));}
@Test void extraFunnelling(){failParse("""
002|   Anon[Y:imm, X:imm, Z:imm]: Box[X,Y]{'b
   |                      ^----
003|     .x -> x; .y -> y; .z: Z -> b.z}

While inspecting generic bounds declaration > method body > method declaration > type declaration body > type declaration > full file
Generic type parameter "Z" is not in scope.
Declared generic type parameters: "X", "Y".
""", List.of("""
Foo:{ .m[X:imm,Y:imm](x: X, y: Y): Box[X,Y] ->
  Anon[Y:imm, X:imm, Z:imm]: Box[X,Y]{'b
    .x -> x; .y -> y; .z: Z -> b.z}
  }
Box[X:imm,Y:imm]:{ .x: X; .y: Y }
"""));}
@Test void funnelWithNarrowerBounds(){fail("""
001| A:{ .m[X:mut,read]: mut Foo[mut X] -> mut Foo[X:mut]:{} }
   |     --------------------------------------^^^^~~~~~~~~~

While inspecting object literal "Foo[_]" > method "A.m" (line 1)
The type "Foo[X]" is invalid.
Generic type argument 1 ("X") does not satisfy the bounds
for generic type parameter "X" in "Foo[_]".
Here "X" can only use capability "mut".
But generic type argument "X" can only use capabilities "mut" or "read".
""", List.of("""
A:{ .m[X:mut,read]: mut Foo[mut X] -> mut Foo[X:mut]:{} }
"""));}
@Test void narrowOuterBoundMutLiteralOk(){ok(List.of("""
Box[X:imm,mut,read]:{ mut .get: X }
A:{ .m[X:imm](x: X): mut Box[X] -> mut Fresh[X:imm,mut,read]:Box[X]{ .get -> x } }
"""));}
@Test void narrowOuterBoundReadLiteralOk(){ok(List.of("""
Box[X:imm,mut,read]:{ read .get: read/imm X }
A:{ .m[X:imm](x: X): read Box[X] -> read Fresh[X:imm,mut,read]:Box[X]{ .get -> x } }
"""));}
@Test void narrowOuterBoundLambdaInsideWiderLiteralOk(){ok(List.of("""
Get[R:imm,mut,read]:{ mut #: R }
Box[X:imm,mut,read]:{ mut .get: mut Get[X] }
A:{ .m[X:imm](x: X): mut Box[X] -> mut Fresh[X:imm,mut,read]:Box[X]{ .get -> { x } } }
"""));}
@Test void narrowOuterBoundCapturingLambdaInsideWiderLiteralOk(){ok(List.of("""
Sink:{ .take[Y:imm,mut,read](y: Y): Sink -> Sink }
Run:{ mut #: Sink }
Box[X:imm,mut,read]:{ mut .get: mut Run }
A:{ .m[X:imm](x: X): mut Box[X] -> mut Fresh[X:imm,mut,read]:Box[X]{ .get -> { Sink.take(x) } } }
"""));}
@Test void wideLiteralBoundIsNotPromotedToIso(){fail("""
002| A:{ .m[X:imm](x: X): iso Box[X] -> mut Fresh[X:imm,mut,read]:Box[X]{ .get -> x } }
   |     -----------------------------------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal "Fresh[_]" > method "A.m(_)" (line 2)
The body of method ".m(_)" of type declaration "A" is an expression returning "mut Fresh[X]".
Object literal is of type "mut Fresh[_]" instead of a subtype of "iso Box[X]".
Hint: write "iso Fresh[_]" if you need an "iso" object literal.
""", List.of("""
Box[X:imm,mut,read]:{ mut .get: X }
A:{ .m[X:imm](x: X): iso Box[X] -> mut Fresh[X:imm,mut,read]:Box[X]{ .get -> x } }
"""));}
@Test void wideLiteralBoundIsoLiteralDoesNotCapture(){fail("""
002| A:{ .m[X:imm](x: X): iso Box[X] -> iso Fresh[X:imm,mut,read]:Box[X]{ .get -> x } }
   |     -----------------------------------------------------------------~~~~~~~~^--

While inspecting parameter "x" > method "Fresh[_].get" (line 2) > method "A.m(_)" (line 2)
Parameter "x" has type "X".
Parameter "x" can observe mutation; thus it cannot be captured in the "iso" object literal "Fresh[_]" (line 2).
Hint: capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
Box[X:imm,mut,read]:{ mut .get: X }
A:{ .m[X:imm](x: X): iso Box[X] -> iso Fresh[X:imm,mut,read]:Box[X]{ .get -> x } }
"""));}
@Test void wideLiteralBoundDropsCaptureNotKindedUnderIt(){fail("""
003| A:{ .m[X:imm](b: Box[X]): read Get[X] -> read Fresh[X:imm,mut,read]:Get[X]{ .get -> b.get } }
   |     ------------------------------------------------------------------------~~~~~~~~^~~~~--

While inspecting parameter "b" > method "Fresh[_].get" (line 3) > method "A.m(_)" (line 3)
Parameter "b" has type "Box[X]".
That type is not well kinded under the generic type parameters of object literal "Fresh[_]" (line 3): "X:imm,mut,read".
The bounds declared by the object literal are all it knows about its generic type parameters,
and thus parameter "b" cannot be captured.
""", List.of("""
Box[X:imm]:{ .get: X }
Get[X:imm,mut,read]:{ read .get: read/imm X }
A:{ .m[X:imm](b: Box[X]): read Get[X] -> read Fresh[X:imm,mut,read]:Get[X]{ .get -> b.get } }
"""));}
@Test void wideLiteralBoundDropsCaptureNotKindedUnderItMut(){fail("""
003| A:{ .m[X:imm](b: Box[X]): mut Get[X] -> mut Fresh[X:imm,mut,read]:Get[X]{ .get -> b.get } }
   |     ----------------------------------------------------------------------~~~~~~~~^~~~~--

While inspecting parameter "b" > method "Fresh[_].get" (line 3) > method "A.m(_)" (line 3)
Parameter "b" has type "Box[X]".
That type is not well kinded under the generic type parameters of object literal "Fresh[_]" (line 3): "X:imm,mut,read".
The bounds declared by the object literal are all it knows about its generic type parameters,
and thus parameter "b" cannot be captured.
""", List.of("""
Box[X:imm]:{ .get: X }
Get[X:imm,mut,read]:{ mut .get: X }
A:{ .m[X:imm](b: Box[X]): mut Get[X] -> mut Fresh[X:imm,mut,read]:Get[X]{ .get -> b.get } }
"""));}
@Test void sameLiteralBoundKeepsCapture(){ok(List.of("""
Box[X:imm]:{ .get: X }
Get[X:imm,mut,read]:{ mut .get: X }
A:{ .m[X:imm](b: Box[X]): mut Get[X] -> mut Fresh[X:imm]:Get[X]{ .get -> b.get } }
"""));}@Test void mutableOuterBoundIsoLiteralDoesNotCapture(){fail("""
002| A:{ .m[X:imm,mut](x: X): iso Box[X] -> iso Fresh[X:imm,mut,read]:Box[X]{ .get -> x } }
   |     ---------------------------------------------------------------------~~~~~~~~^--

While inspecting parameter "x" > method "Fresh[_].get" (line 2) > method "A.m(_)" (line 2)
Parameter "x" has type "X".
Parameter "x" can observe mutation; thus it cannot be captured in the "iso" object literal "Fresh[_]" (line 2).
Hint: capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
Box[X:imm,mut,read]:{ mut .get: X }
A:{ .m[X:imm,mut](x: X): iso Box[X] -> iso Fresh[X:imm,mut,read]:Box[X]{ .get -> x } }
"""));}
}
