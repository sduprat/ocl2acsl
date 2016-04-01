# Assumptions for translation #

C code generated from the UML model must be generated according to the following assumptions. This tool does not provide an implementation of these patterns but strongly depends on them for contract generation.

## Datatypes ##

We assume that datatypes are translated to C structs. A property of type T is translated to a field of type T. A collection property is translated to a pointer field T`*` if it has a variable size, to an array T`[`n`]` otherwise.  If the size is variable, the struct must also own a property of type int named size`_`{name`_`array} indicating the size of the array. If it is constant, it must be defined using a macro named DATATYPE\_PROP\_SIZE.

Let's consider the following example :

<img src='https://svn.codespot.com/a/eclipselabs.org/ocl2acsl/wiki/datatype.PNG' />

We assume the C generation is as follows :

```

#define TYPE1_CSTARRAY_SIZE 5
typedef struct Type1 {
int id;
int* array;
int size_array;
int cstArray[TYPE1_CSTARRAY_SIZE];
} Type1;
```

## Associations ##
We assume that compositions are translated the same way as attributes while aggregations use pointers. An aggregation of type T is translated to a pointer field of type T`*`. If it has a multiplicity of n, it is translated to an array of pointers of size n. Otherwise, if it has a variable size it is translated to a pointer on pointers. We keep the same assumptions for the size of arrays. Let's consider the following associations between two datatypes :

<img src='https://svn.codespot.com/a/eclipselabs.org/ocl2acsl/wiki/assocs.PNG' />

We assume the corresponding C code is as follows :

```

#define DATATYPE2_CN_SIZE 5
#define DATATYPE2_AN_SIZE 9

typedef struct DataType1 {
int id;
} DataType1;

typedef struct DataType2 {
DataType1 c1;
DataType1 cN[DATATYPE2_CN_SIZE];
DataType1* c;
DataType1* a1;
DataType1* aN[DATATYPE2_AN_SIZE];
DataType1** a;
int size_c;
int size_a;
} DataType2;
```

## Classes and operations ##
Classes are translated to C modules, their properties are translated to global variables but with the same assumptions as datatypes. Let's consider the following class example :

<img src='https://svn.codespot.com/a/eclipselabs.org/ocl2acsl/wiki/class.PNG' />

The corresponding C code is given below :

```

#define CLASS1_PROP1_SIZE 5
int prop1[CLASS1_PROP1_SIZE];
void test(){}
```

In operations, all parameters of primitive types and that are OUT or INOUT, are transformed into pointers. When a parameter is a collection of constant size, a macro should be included to the C code named OPERATION\_PARAM\_SIZE. If the collection is of variable size, the operation must also own a paramter named size`_`{name`_`array}.

Below examples of static operations translation :

|```
op1(in n1:Integer, inout n2:Integer)```|```
void op1(int n1, int* n2);```|
|:------------------------------------------|:--------------------------------|
|```
op2(in obj1:Type1, inout obj2:Type1)```|```
void op2(Type1 obj1, Type1* obj2);```|
|```
op3(in cstArray:Integer[5])```         |```
#define OP3_CSTARRAY_SIZE 5``````
void op3(int cstArray[OP3_CSTARRAY_SIZE]);```|
|```
op4(in array:Integer[*],in size_array:Integer)```|```
void op4(int* array, int size_array);```|

# Rules for translation #

| **OCL expression** | **Details** | **Remarks and assumptions** | **OCL Example** | **ACSL translation** |
|:-------------------|:------------|:----------------------------|:----------------|:---------------------|
| PropertyCallExp    | Attribute access | See assumptions and example above|```
obj.id / obj.array -> at(i)``` |```
obj.id / obj.array[i]```|
|                    | Composition |See assumptions and example above |```
obj.c1.id / (obj.cN -> at(i)).id / (obj.c -> at(i)).id``` |```
obj.c1.id / obj.cN[i].id / obj.c[i].id```|
|                    | Aggregation | See assumptions and example above |```
obj.a1.id / (obj.aN -> at(i)).id / (obj.a -> at(i)).id```  |```
(*obj.a1).id / (*obj.aN[i]).id / (*obj.a[i]).id``` |
|                    | PRE label	  |                             |```
x@pre ```    |```
\old(x)```        |
| OperationCallExp   | or / xor/ and/ not/ implies | On booleans                 |                 |```
|| / ^^ / && / ! /  ==>```|
|                    | +/-         | On integers/reals           |                 |```
+/-```            |
|                    | **//**| On integers/reals           |                 |```
*//```            |
|                    | < > <= >=   | On integers/reals           |                 |```
< > <= >=```      |
|                    | Min/Max     | On integers/reals           |                 |```
\Min \Max```      |
|                    | Mod         | On integers                 |                 |```
%```              |
|                    | abs         | On reals                    |                 |```
Abs```            |
|                    | first/last  |                             |```
a -> First()/Last()```|```
a[0] a[size_a-1]```|
|                    | at          |                             |```
a -> at(i)``` |```
a[i]```           |
|                    | Includes    | The source of the operator must be one of the following: |                 |
|                    |             | 1- An array that is a parameter of the operation |```
a -> includes(e)```|```
\exists int i;  0 <= i <= size_a-1 && a[i]=e```|
|                    |             | 2- A property that is an array |```
obj.prop -> includes(e)```|```
\exists int i;  0 <= i <= obj.size_prop-1 && obj.prop[i]=e```|
|                    | Excludes    | Idem (a is either a parameter or a property)|```
a -> excludes(e)``` |```
\forall int i;  0 <= i <= size_a-1 ==> a[i]!=e```|
|                    | <> on collections | Idem (a,b are either parameters or properties)|```
a <> b```    |```
size_a!=size_b``````
|| \exists int i;  0 <= i <= size_a-1 && a[i]!=b[i]```|
|                    | "=" on collections | Idem (a,b are either parameters or properties)|```
a = b```     |```
size_a==size_b``````
&& \forall int i;  0 <= i <= size_a-1 ==> a[i]=b[i]```|
|                    | IncludesAll | Idem (a,b either parameters or properties) | ```
a -> includesAll(b)```|```
\forall int i;  0 <= i <= size_b-1``````
==> \exists int j;  0 <= j <= size_a-1 && a[j]=b[i]```|
|                    | ExcludesAll | Idem (a,b are either parameters or properties)| ```
a -> excludesAll(b)```|```
\forall int i;  0 <= i <= size_b-1``````
==> \forall int j;  0 <= j <= size_a-1 ==> a[j]!=b[i]```|
|                    | isEmpty     | Idem (a is either a parameter or a property) |```
a -> isEmpty()```|```
size_a = 0```     |
|                    | notEmpty    | Idem (a is either a parameter or a property)|```
a -> notEmpty()```|```
size_a != 0```    |
|                    | size        | Idem (a is either a parameter or a property) |```
a -> size()``` |```
size_a```         |
| IteratorExp        | Forall      | The source of the operator must be one of the following: |                 |
|                    |             | 1- A sequence of integers n1..n2 that indexes an array in the body of the forAll | ```
Sequence(n1..n2) -> forAll( i | body(a -> at (i))``` |```
\forall int i; n1 <= i <= n2 ==> body(a[i]);```|
|                    |             | 2- An array that is a parameter of the operation |```
a -> forAll(x | body(x))```|```
\forall int i; 0 <= i <= size_a-1 ==> body(a[i]);```|
|                    |             | 3- A property that is an array |```
obj.prop -> forAll(x | body(x))``` |```
\forall int i; 0 <= i <= obj.size_prop-1 ==> body(obj.prop[i]);```|
|                    | Exists      | Idem                        | Idem with \exists |                      |
|                    | One         | The source of the operator must be one of the following: |                 |
|                    |             | 1- An array that is a parameter of the operation |```
a -> one(x | f(x))``` |```
(\exists int i; 0<=i<=size_a-1 && f(a[i]))``````
&& (\forall int j; 0<=j<=size_a-1 && j!=i ==> !f(a[i])```|
|                    |             | 2- A property that is an array |```
obj.prop -> one(x | f(x))``` |```
(\exists int i; 0<=i<=obj.size_prop-1 && f(obj.prop[i]))``````
&& (\forall int j; 0<=j<=obj.size_prop-1 && j!=i ==> !f(obj.prop[i])``` |
| VariableExp        | Parameter   | Generation of assigns clauses for modifiable parameters and valid clauses <br> for pointers and arrays. <table><thead><th><pre><code>inout x, in array</code></pre></th><th><pre><code>assigns(*x),\valid(array+(0..size_array))</code></pre></th></thead><tbody>
<tr><td>                    </td><td> Result      </td><td>                             </td><td><pre><code>result</code></pre> </td><td><pre><code>\result</code></pre></td></tr>
<tr><td> IfExp              </td><td>             </td><td>                             </td><td><pre><code>if condition then x else y endif</code></pre></td><td><pre><code>condition?x:y</code></pre></td></tr>
<tr><td> LetExp             </td><td>             </td><td>                             </td><td><pre><code>let x: Type = exp in body</code></pre></td><td><pre><code>\let id=exp;body;</code></pre></td></tr>