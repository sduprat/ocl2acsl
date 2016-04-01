# Ocl2acsl class #

The provided constructor Ocl2acsl( ) sets up the environment for OCL translation. Methods in this class translate OCL constraints of type org.eclipse.uml2.uml.Constraint into string representations of the corresponding ACSL expressions. The class also explores the operations of the model that are objects of type org.eclipse.uml2.uml.Operation in order to generate contract clauses stating the validity of pointers and arrays and the memory locations the operation is allowed to modify.

```java
String prepost2acsl(Constraint cons)``` Generates the ACSL expression that corresponds to the given pre/post condition
```java
String inv2acsl(Constraint cons)```
Generates an ACSL expression equivalent to the given OCL invariant

```java
ArrayList <String> generateValidClauses (Operation op) ``` Returns a list of ACSL valid clauses corresponding to the pointers introduced to represent modifiable parameters

```java
ArrayList<String> getAssignedParameters (Operation op) ``` Returns a list of parameters’ names that correspond to the parameters the operation is allowed to modify

```java
ArrayList<String> generateArrayValidClauses (Operation op)``` Returns a list of ACSL valid clauses corresponding to the arrays manipulated by the operation

These methods instantiate an OCLVisitor that explores the constraint and returns the resulting ACSL expression. More details on the translation can be found in the table at the end of this wiki.

# ACCELEO module #

Ocl2acsl methods require constraints defined in the context of a class diagram. Therefore, in order to use the generator, we have to parse the UML model. The ACCELEO module OCL2ACSL parses the model and generates for each class a ".fc" file containing the contracts of all its operations.

**StaticOcl2ACSL**: This class is used to link the ACCELEO module and the OCL2ACSL tool. It instantiates an OCL2acsl object and provides static methods to perform the translation.

**Wrapper**: A wrapper “wrapper.mtl” is provided to invoke the java methods for translation. For example, the prepost2acsl method is wrapped into an ACCELEO query as follows:

<img src='https://svn.codespot.com/a/eclipselabs.org/ocl2acsl/wiki/wrapper.png' height='100' width='500' />


**Generator**: The “generate.mtl” file parses the model and generates for each class a “.fc” file containing the different contracts.

<img src='https://svn.codespot.com/a/eclipselabs.org/ocl2acsl/wiki/generator.PNG' height='200' width='500' />

A contract contains four different parts:
  * Valid clauses: They express which pointers are required to be valid before the execution of the method,  and are generated using getValidClauses( )

  * Requires clauses: Pre-conditions of the operation, generated using getPre( )

  * Assigns clauses: Memory locations the operation is allowed to modify, generated using getAssignsClauses( )

  * Ensures clauses: Post-conditions of the operation, generated using getPost( )

These three templates invoke the wrapper’s queries and add the corresponding ACSL keywords to the result. Below is how getPre() works :

<img src='https://svn.codespot.com/a/eclipselabs.org/ocl2acsl/wiki/getpre.PNG' height='100' width='500' />