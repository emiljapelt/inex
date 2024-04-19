# Expressions
In Seplin expressions are the only constructs which have some inherent value. They come in two flavours, 'value' and 'reference', where 'value' is just a value and 'reference' is a reference to some value.

## Index
- [Expressions](#expressions)
  - [Index](#index)
  - [Bool](#bool)
  - [Int](#int)
  - [Char](#char)
  - [String](#string)
  - [Null](#null)
  - [Access](#access)
  - [ArrayAccess](#arrayaccess)
  - [StructAccess](#structaccess)
  - [BinaryOperation](#binaryoperation)
  - [UnaryOperation](#unaryoperation)
  - [Ternary](#ternary)
  - [ArraySize](#arraysize)
  - [Read](#read)
  - [NewArray](#newarray)
  - [ArrayLiteral](#arrayliteral)
  - [NewStruct](#newstruct)
  - [StructLiteral](#structliteral)
  - [AnonymousRoutine](#anonymousroutine)
- [Binary operators](#binary-operators)
- [Unary operators](#unary-operators)

___
## Bool
**Flavour:** value
<br>
**Syntax:** true \| false
<br>
**Type:** _bool_
<br>
**Explaination:** A boolean literal.
<br>
**Examples:**
```
true
false
```
___
## Int
**Flavour:** value
<br>
**Syntax:** _n_
<br>
**Type:** _int_
<br>
**Explaination:** An integer literal.
<br>
**Examples:**
```
0
1337
```
___
## Char
**Flavour:** value
<br>
**Syntax:** '_n_' \| '\\_n_'
<br>
**Type:** _char_
<br>
**Explaination:** A character literal.
<br>
**Examples:**
```
'a'
'\n'
```
___
## String
**Flavour:** value
<br>
**Syntax:** " .* "
<br>
**Type:** _char_ [ ]
<br>
**Explaination:** A string is simply a char array. Escape characters are not supported yet.
<br>
**Examples:**
```
"Hello world!"
"The next one is the empty string"
""
```
___
## Null
**Flavour:** reference
<br>
**Syntax:** null
<br>
**Type:** N/A
<br>
**Explaination:** A reference to nothing.
<br>
**Examples:**
```
null
```
___
## Access
**Flavour:** reference
<br>
**Syntax:**
<br>
_name_
<br>
_context_alias_ # _name:
<br>
**Type:** the type of the accessed name.
<br>
**Explaination:** Access a declared name.
<br>
**Examples:**
```
x
my_array
other_context#my_routine
```
___
## ArrayAccess
**Flavour:** reference
<br>
**Syntax:** _reference_ [ _int_expression_ ]
<br>
**Type:** the type of the array elements.
<br>
**Explaination:** Access an index in an array, the index must be an integer.
<br>
**Examples:**
```
x[0]
my_array[4]
```
___
## StructAccess
**Flavour:** reference
<br>
**Syntax:** _reference_ . _field_
<br>
**Type:** the type of the field.
<br>
**Explaination:** Access a field of a struct.
<br>
**Examples:**
```
l.head
my_tuple.fst
```
___
## BinaryOperation
**Flavour:** value
<br>
**Syntax:** _expression_ _operator_ _expression_
<br>
**Type:** [look at this table](#binary-operators)
<br>
**Explaination:** Compute some value from two expressions.
<br>
**Examples:**
```
1 + 2
true && false
```
___
## UnaryOperation
**Flavour:** value
<br>
**Syntax:** _operator_ _expression_
<br>
**Type:** [look at this table](#unary-operators)
<br>
**Explaination:** Compute some value from a single expression.
<br>
**Examples:**
```
!true
-3
```
___
## Ternary
**Flavour:** value
<br>
**Syntax:** _bool_condition_ ? _expression_ : _expression_
<br>
**Type:** The type of _expression_
<br>
**Explaination:** Compute some value depending on the result of _bool_condition_. The _expression_'s must be of equatable types.
<br>
**Examples:**
```
true ? 1 : 2
i > 1 ? true : false
```
___
## ArraySize
**Flavour:** value
<br>
**Syntax:** \| _expression_ \|
<br>
**Type:** _int_
<br>
**Explaination:** Get the size of an array.
<br>
**Examples:**
```
|a|
|my_arrays[1]|
```
___
## Read
**Flavour:** value
<br>
**Syntax:** read<_type_>
<br>
**Type:** _type_
<br>
**Explaination:** Get user input, only simple types are currently supported.
<br>
**Examples:**
```
read<int>
read<char>
```
___
## NewArray
**Flavour:** value
<br>
**Syntax:** new _type_ [ _int_expression_ ]
<br>
**Type:** _type_[ ]
<br>
**Explaination:** Create a new empty array of some size.
<br>
**Examples:**
```
new int[5]
new tuple<int,int>[5]
```
___
## ArrayLiteral
**Flavour:** value
<br>
**Syntax:** [ _expressions_ ]
<br>
**Type:** depends on the expressions.
<br>
**Explaination:** Create a filled array. All expressions must be of the same type.
<br>
**Examples:**
```
[1, 2, 3]
[[1,2], [3,4], [4,5]]
```
___
## NewStruct
**Flavour:** value
<br>
**Syntax:** new _struct_name_ <_type_arguments_> ( arguments )
<br>
**Type:** _stuct_name_<_type_arguments_>
<br>
**Explaination:** Create a new struct instance. If the type arguments are left out, the compiler will attempt to infer them.
<br>
**Examples:**
```
new list<int>(1,null)
new tuple(1,2)
```
___
## StructLiteral
**Flavour:** value
<br>
**Syntax:** { _expressions_ }
<br>
**Type:** any struct type matching the structure of the expression.
<br>
**Explaination:** Create a new struct instance. Cannot be typed on its own.
<br>
**Examples:**
```
{1,2}
{1, {2, null}}
```
___
## AnonymousRoutine
**Flavour:** value
<br>
**Syntax:**
<br>
( _parameters_ ) [_block_](StatementsAndDeclarations.md#block)
<br>
< _type_variables_ > ( _parameters_ ) [_block_](StatementsAndDeclarations.md#block)
<br>
**Type:** Routine type of the types in _parameters_.
<br>
**Explaination:** Declares an unnamed routine. Parameters to routines can be of a routine type, making it a higher-order routine.
<br>
**Examples:**
```
(i: int) { i +:= 10; }

<T>(a: T, b: T) {
  tmp ::= a;
  a := b;
  b := tmp;
}

(i: int, routine: (int)) { 
  routine(i); 
}
```
___


# Binary operators
| Operator | Left types | Right types | Result type | Explaination |
| --- | --- | --- | --- | --- |
| + | int | int | int | Addition |
| - | int | int | int | Subtraction |
| * | int | int | int | Multiplication |
| / | int | int | int | Division |
| % | int | int | int | Modolo |
| = | * | * | bool | Equivalence, can also be used for null checking |
| != | * | * | bool | Non Equivalence, can also be used for null checking |
| < | int | int | bool | Less than |
| <= | int | int | bool | Less than or equal |
| > | int | int | bool | Greater than |
| >= | int | int | bool | Greate than or equal |
| && | bool | bool | bool | Conjunction |
| \|\| | bool | bool | bool | Disjunction | 
_* = any type_

# Unary operators
| Operator | Types | Result type| Explaination |
| --- | --- | --- | --- |
| ! | bool | bool | Negation |
| - | int | int | Negation |
| $ | * | * | Get the value of the operand, useful for dereferencing |
_* = any type_
