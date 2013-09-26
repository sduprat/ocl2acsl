/*****************************************************************************
 * Copyright (c) 2013 Atos.
 *
 *    
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 *
 *****************************************************************************/

package org.eclipse.ocl2acsl;

import org.eclipse.emf.common.util.EList;
import org.eclipse.ocl.expressions.AssociationClassCallExp;
import org.eclipse.ocl.expressions.BooleanLiteralExp;
import org.eclipse.ocl.expressions.CollectionItem;
import org.eclipse.ocl.expressions.CollectionKind;
import org.eclipse.ocl.expressions.CollectionLiteralExp;
import org.eclipse.ocl.expressions.CollectionLiteralPart;
import org.eclipse.ocl.expressions.CollectionRange;
import org.eclipse.ocl.expressions.EnumLiteralExp;
import org.eclipse.ocl.expressions.FeatureCallExp;
import org.eclipse.ocl.expressions.IfExp;
import org.eclipse.ocl.expressions.IntegerLiteralExp;
import org.eclipse.ocl.expressions.InvalidLiteralExp;
import org.eclipse.ocl.expressions.IterateExp;
import org.eclipse.ocl.expressions.IteratorExp;
import org.eclipse.ocl.expressions.LetExp;
import org.eclipse.ocl.expressions.MessageExp;
import org.eclipse.ocl.expressions.NullLiteralExp;
import org.eclipse.ocl.expressions.OCLExpression;
import org.eclipse.ocl.expressions.OperationCallExp;
import org.eclipse.ocl.expressions.PropertyCallExp;
import org.eclipse.ocl.expressions.RealLiteralExp;
import org.eclipse.ocl.expressions.StateExp;
import org.eclipse.ocl.expressions.StringLiteralExp;
import org.eclipse.ocl.expressions.TupleLiteralExp;
import org.eclipse.ocl.expressions.TupleLiteralPart;
import org.eclipse.ocl.expressions.TypeExp;
import org.eclipse.ocl.expressions.UnlimitedNaturalLiteralExp;
import org.eclipse.ocl.expressions.UnspecifiedValueExp;
import org.eclipse.ocl.expressions.Variable;
import org.eclipse.ocl.expressions.VariableExp;
import org.eclipse.ocl.uml.SequenceType;
import org.eclipse.ocl.uml.impl.TypeTypeImpl;
import org.eclipse.ocl.utilities.AbstractVisitor;
import org.eclipse.ocl.utilities.ExpressionInOCL;
import org.eclipse.uml2.uml.AggregationKind;
import org.eclipse.uml2.uml.CallOperationAction;
import org.eclipse.uml2.uml.Classifier;
import org.eclipse.uml2.uml.Constraint;
import org.eclipse.uml2.uml.DataType;
import org.eclipse.uml2.uml.Enumeration;
import org.eclipse.uml2.uml.EnumerationLiteral;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Parameter;
import org.eclipse.uml2.uml.ParameterDirectionKind;
import org.eclipse.uml2.uml.PrimitiveType;
import org.eclipse.uml2.uml.Property;
import org.eclipse.uml2.uml.SendSignalAction;
import org.eclipse.uml2.uml.State;
import org.eclipse.uml2.uml.Type;

/**
 * OCLVisitor visits an OCLExpression and generates the corresponding ACSL code.
 * 
 * @author A560169
 * 
 */
public class OCLVisitor
		extends
		AbstractVisitor<String, Classifier, Operation, Property, EnumerationLiteral, Parameter, State, CallOperationAction, SendSignalAction, Constraint> {

	/**
	 * Visits a {@link PropertyCallExp}.
	 * 
	 * @param callExp
	 *            The {@link PropertyCallExp} to visit.
	 * @return A String representing the property call in ACSL
	 */
	@Override
	public String visitPropertyCallExp(
			PropertyCallExp<Classifier, Property> callExp) {
		Property property = callExp.getReferredProperty();
		OCLExpression<Classifier> sourceExp = callExp.getSource();
		if (sourceExp == null) {
			return maybeAtPre(callExp, property.getName());
		} else {
			if (sourceExp.toString().equals("self")) {
				// Access to module property => Global Variable
				return maybeAtPre(callExp, property.getName());
			} else {
				// Access to property of parameter
				String source = sourceExp.accept(this);
				AggregationKind kind = property.getAggregation();
				// Composition or attribute
				if (callExp.getSource().getType() instanceof TypeTypeImpl){
					return maybeAtPre(callExp,property.getName());
				}
				if (kind == AggregationKind.COMPOSITE_LITERAL
						|| kind == AggregationKind.NONE_LITERAL)
					return maybeAtPre(callExp,
								"(" + source + ")." + property.getName());
				// Aggregation
				if (kind == AggregationKind.SHARED_LITERAL) {
					// Aggregation with multiplicity 1 == pointer
					if (property.getLower() == property.getUpper()
							&& property.getLower() == 1)
						return maybeAtPre(callExp,
								"*((" + source + ")." + property.getName() + ")");
					// Aggregation with multiplicity n..n or 0..* == array of
					// pointers
					// For now, we return the name of the array and we only apply
					// the * after indexing the array
					// See maybePointerProperty
					else
						return maybeAtPre(callExp,
								"(" + source + ")." + property.getName());
				}
			}		
			throw new IllegalArgumentException("Unhandled kind of property"
					+ property.getName() + property.getAggregation());
		}
	}

	/*
	 * Checks if an expression is marked with the Pre label
	 */
	private String maybeAtPre(FeatureCallExp<Classifier> mpc, String base) {
		return mpc.isMarkedPre() ? "\\old(" + base + ")" : base;
	}

	/**
	 * Visits an {@link OperationCallExp}.
	 * 
	 * @param callExp
	 *            The {@link OperationCallExp} to visit
	 * @return A String representing the translation of the operation in ACSL
	 */
	@SuppressWarnings("unchecked")
	@Override
	public String visitOperationCallExp(
			OperationCallExp<Classifier, Operation> callExp) {

		String oper = ocl2acslOperator(callExp.getReferredOperation().getName());

		if (oper.equals("includes") || oper.equals("excludes")) {
			return visitIncludesExcludesCall(callExp, oper);
		}
		if ((oper.equals("==") || oper.equals("!="))
				&& callExp.getSource().getType() instanceof SequenceType) {
			return visitEqualNonEqualCall(callExp, oper);
		}
		if (oper.equals("isEmpty") || oper.equals("notEmpty")) {
			return visitIsEmptyNotEmptyCall(callExp, oper);
		}
		if (oper.equals("includesAll") || oper.equals("excludesAll")) {
			return visitIncludesAllExcludesAllCall(callExp, oper);
		}
		if (oper.equals("size")) {
			String size = getSizeParamName(callExp.getSource());
			return size;
		}
		if (oper.equals("last")) {
			String size = getSizeParamName(callExp.getSource());
			String source = callExp.getSource().accept(this);
			String ub = size + "-1";
			String base = source + "[" + ub + "]";
			return maybePointerProperty(callExp.getSource(), base);
		}
		if (oper.equals("first")) {
			String op1 = callExp.getSource().accept(this);
			String base = op1 + "[0]";
			return maybePointerProperty(callExp.getSource(), base);
		}
		if (oper.equals("at")) {
			boolean addPre = false;
			OCLExpression<Classifier> source = callExp.getSource();
			if (source instanceof PropertyCallExp && ((PropertyCallExp<Classifier, Property>) source).isMarkedPre()) {
				addPre = true;
				((PropertyCallExp<Classifier, Property>) source).setMarkedPre(false);
			}
			String op1 = source.accept(this);
			String op2 = callExp.getArgument().get(0).accept(this);
			op1 = maybePointerProperty(source, op1);
			String res = op1 + "[" + op2 + "]";
			if (addPre) res = "\\old(" + res + ")";
			return res;
		}
		if (oper.equals("oclAsType")) return callExp.getSource().accept(this);
		if (oper.equals("subSequence")) {
			String source = callExp.getSource().accept(this);
			String offset = callExp.getArgument().get(0).accept(this);
			source = maybePointerProperty(callExp.getSource(), source);
			return source + " + " + offset;
		}
		if (isUnaryOperator(callExp)){
			String op1 = callExp.getSource().accept(this);
			if (needParenthesis(callExp.getSource(), oper)){
				op1 = "(" + op1 + ")";
			}
			if (Ocl2acsl.acslOperationNotationType.containsKey(oper)){
				if (Ocl2acsl.acslOperationNotationType.get(oper).equals("prefix")){
					return  oper + op1 ;
				}if (Ocl2acsl.acslOperationNotationType.get(oper).equals("procedural")){
					return oper + "(" + op1 + ")" ;
				} else {
					return "Error for an unary operator Notation type Should be infix or procedural" ;
				}
			}
			if (oper.equals("-") || oper.equals("!")){
				return  oper + op1 ;
			} else {
				return oper + "(" + op1 + ")" ;
			}
		}
		if (isBinaryOperator(callExp)){
			String op1 = callExp.getSource().accept(this);
			if (needParenthesis(callExp.getSource(), oper)){
				op1 = "(" + op1 + ")";
			}
			String op2 = callExp.getArgument().get(0).accept(this);
			if (needParenthesis(callExp.getArgument().get(0), oper)){
				op2 = "(" + op2 + ")";
			 	}
			if (isInfix(oper)){
				return op1 + " " + oper+ " " + op2  ;
			 	} else {
			 		return oper + "(" + op1 + ", " + op2 +")" ;
			 	}
		}
		throw new IllegalArgumentException("Operator " + oper
				+ " not supported");
	}

	/*
	 * Translates an OCL operator to its equivalent in ACSL
	 */
	private String ocl2acslOperator(String oper) {
		if (oper.equals("="))
			return "==";
		if (oper.equals("<>"))
			return "!=";
		if (oper.equals("or"))
			return "||";
		if (oper.equals("xor"))
			return "^^";
		if (oper.equals("and"))
			return "&&";
		if (oper.equals("not"))
			return "!";
		if (oper.equals("implies"))
			return "==>";
		if (oper.equals("div"))
			return "/";
		if (oper.equals("mod"))
			return "%";
		if (oper.equals("round"))
			return "ceil";
		if (Ocl2acsl.acslOperationName.containsKey(oper)) return Ocl2acsl.acslOperationName.get(oper);
		return oper;
	}

	/*
	 * Checks if an operator should be written infix-style in ACSL
	 */
	private boolean isInfix(String oper) {
		if (Ocl2acsl.acslOperationNotationType.containsKey(oper)) {
			return Ocl2acsl.acslOperationNotationType.get(oper).equals("infix");
		}
		return oper.equals("*") || oper.equals("/") || oper.equals("+")
				|| oper.equals("-") || oper.equals("<") || oper.equals(">")
				|| oper.equals("<=") || oper.equals(">=") || oper.equals("==")
				|| oper.equals("!=") || oper.equals("||") || oper.equals("^^")
				|| oper.equals("&&") || oper.equals("==>") || oper.equals("%");
	}

	/*
	 * Checks if an operator is a unary operator
	 */
	private boolean isUnaryOperator(
			OperationCallExp<Classifier, Operation> callExp) {
		return (callExp.getArgument().size() == 0);
	}

	/*
	 * Checks if an operator is a binary operator
	 */
	private boolean isBinaryOperator(
			OperationCallExp<Classifier, Operation> callExp) {
		return (callExp.getArgument().size() == 1);
	}

	/*
	 * Returns the priority of operators. The priority of the elementary
	 * operators is taken from the ACSL specification
	 */
	private int getPriority(String oper) {
		if (oper.equals("at") || oper.equals("first") || oper.equals("size"))
			return 110;
		if (oper.equals("!") || oper.equals("#-"))
			return 100;
		if (oper.equals("*") || oper.equals("/") || oper.equals("%"))
			return 90;
		if (oper.equals("+") || oper.equals("-"))
			return 80;
		if (oper.equals(">") || oper.equals("<") || oper.equals(">=")
				|| oper.equals("<="))
			return 70;
		// The notEmpty/isEmpty is translated to ==,!=
		if (oper.equals("==") || oper.equals("!=") || oper.equals("notEmpty")
				|| oper.equals("isEmpty"))
			return 60;
		// The == for collections is translated to a conjunction
		if (oper.equals("&&") || oper.equals("#=="))
			return 50;
		if (oper.equals("^^"))
			return 40;
		// The != for collections is translated to a disjunction
		if (oper.equals("||") || oper.equals("#!="))
			return 30;
		if (oper.equals("==>"))
			return 20;
		if (oper.equals("if"))
			return 10;
		// All these operators are translated into forall/exists
		if (oper.equals("forAll") || oper.equals("exists")
				|| oper.equals("includes") || oper.equals("excludes")
				|| oper.equals("includesAll") || oper.equals("excludesAll")
				|| oper.equals("one"))
			return 0;
		return 120;
	}

	/*
	 * Checks if an expression needs parenthesis to respect the order of
	 * operations
	 */
	@SuppressWarnings("unchecked")
	private boolean needParenthesis(OCLExpression<Classifier> exp, String oper) {
		if (exp instanceof OperationCallExp) {
			String op2 = ocl2acslOperator(((OperationCallExp<Classifier, Operation>) exp)
					.getReferredOperation().getName());
			if (op2.equals("-")
					&& isUnaryOperator((OperationCallExp<Classifier, Operation>) exp))
				op2 = "#-";
			if ((op2.equals("==") || op2.equals("!="))
					&& ((OperationCallExp<Classifier, Operation>) exp)
							.getSource().getType() instanceof SequenceType)
				op2 = "#" + op2;
			if (getPriority(op2) < getPriority(oper))
				return true;
		}
		if (exp instanceof IteratorExp) {
			String op2 = exp.getName();
			if (getPriority(op2) < getPriority(oper))
				return true;
		}
		if (exp instanceof IfExp) {
			String op2 = "if";
			if (getPriority(op2) < getPriority(oper))
				return true;
		}
		return false;
	}

	/**
	 * Visits an {@link OperationCallExp} containing the includesAll/excludesAll
	 * OCL operators.
	 * <p>
	 * <code>a -> includesAll(b)</code> generates the following ACSL contract :
	 * <code>\forall int i; 0 <= i <= size_b-1 ==> (\exists int j; 0 <= j <= size_a-1 && a[j]==b[i])</code>
	 * <p>
	 * <code>a -> excludesAll(b)</code> generates the following ACSL contract :
	 * <code>\forall int i; 0 <= i <= size_b-1 ==> (\forall int j; 0 <= j <= size_a-1 ==> a[j]!=b[i])</code>
	 * 
	 * @param callExp
	 *            The {@link OperationCallExp} to visit
	 * @param oper
	 *            The type of the operator {IncludesAll,ExcludesAll}
	 * @return A string representing the translation of the operator in ACSL
	 */
	public String visitIncludesAllExcludesAllCall(
			OperationCallExp<Classifier, Operation> callExp, String oper) {
		OCLExpression<Classifier> array1 = callExp.getSource();
		OCLExpression<Classifier> array2 = callExp.getArgument().get(0);
		Boolean includesAll = oper.equals("includesAll");
		String size1 = getSizeParamName(array1);
		String size2 = getSizeParamName(array2);
		String ub1 = size1 + "-1";
		String ub2 = size2 + "-1";
		String tab1 = array1.accept(this) + "[j]";
		String tab2 = array2.accept(this) + "[i]";
		tab1 = maybePointerProperty(array1, tab1);
		tab2 = maybePointerProperty(array2, tab2);
		if (includesAll)
			return "\\forall int i; 0 <= i <= " + ub2
					+ " ==> (\\exists int j; 0<= j <= " + ub1 + " && " + tab1
					+ " == " + tab2 + ")";
		else
			return "\\forall int i; 0 <= i <= " + ub2
					+ " ==> (\\forall int j; 0<= j <= " + ub1 + " ==> " + tab1
					+ " != " + tab2 + ")";
	}

	/**
	 * Visits an {@link OperationCallExp} containing the isEmpty/notEmpty OCL
	 * operators.
	 * <p>
	 * <code>a -> isEmpty()</code> generates the following ACSL contract :
	 * <code>size_a == 0</code>
	 * <p>
	 * <code>a -> notEmpty()</code> generates the following ACSL contract :
	 * <code>size_a != 0</code>
	 * 
	 * @param callExp
	 *            The {@link OperationCallExp} to visit
	 * @param oper
	 *            The type of the operator {isEmpty,notEmpty}
	 * @return A string representing the translation of the operator in ACSL
	 */
	public String visitIsEmptyNotEmptyCall(
			OperationCallExp<Classifier, Operation> callExp, String oper) {
		OCLExpression<Classifier> array = callExp.getSource();
		String size = getSizeParamName(array);
		Boolean isEmpty = oper.equals("isEmpty");
		return isEmpty ? (size + " == 0") : (size + " !=0");
	}

	/**
	 * Visits an {@link OperationCallExp} containing the =/<> OCL operators
	 * applied to collections.
	 * <p>
	 * <code>a = b</code> generates the following ACSL contract :
	 * <code>size_a == size_b && (\forall int i; 0 <= i <= size_a-1 ==> a[i]==b[i])</code>
	 * <p>
	 * <code>a <> b</code> generates the following ACSL contract :
	 * <code>size_a != size_b || (\exists int i; 0 <= i <= size_a-1 && a[i]!=b[i])</code>
	 * 
	 * @param callExp
	 *            The {@link OperationCallExp} to visit
	 * @param oper
	 *            The type of the operator {==,!=}
	 * @return A string representing the translation of the operator in ACSL
	 */
	public String visitEqualNonEqualCall(
			OperationCallExp<Classifier, Operation> callExp, String oper) {
		OCLExpression<Classifier> array1 = callExp.getSource();
		OCLExpression<Classifier> array2 = callExp.getArgument().get(0);
		Boolean equals = oper.equals("==");
		String size1 = getSizeParamName(array1);
		String size2 = getSizeParamName(array2);
		String ub1 = size1 + "-1";
		String tab1 = array1.accept(this) + "[i]";
		String tab2 = array2.accept(this) + "[i]";
		tab1 = maybePointerProperty(array1, tab1);
		tab2 = maybePointerProperty(array2, tab2);
		if (equals)
			return size1 + "==" + size2 + " && (\\forall int i; 0 <= i <= "
					+ ub1 + " ==>" + tab1 + " == " + tab2 + ")";
		else
			return size1 + "!=" + size2 + " || (\\exists int i; 0 <= i <= "
					+ ub1 + " && " + tab1 + " != " + tab2 + ")";
	}

	/**
	 * Visits an {@link OperationCallExp} containing the includes/excludes OCL
	 * operators.
	 * <p>
	 * <code>a -> includes(n)</code> generates the following ACSL contract :
	 * <code>\exists int i; 0 <= i <= size_a-1 && a[i]==n</code>
	 * <p>
	 * <code>a -> excludes(n)</code> generates the following ACSL contract :
	 * <code>\forall int i; 0 <= i <= size_a-1 ==> a[i]!=n</code>
	 * 
	 * @param callExp
	 *            The {@link OperationCallExp} to visit
	 * @param oper
	 *            The type of the operator {includes,excludes}
	 * @return A string representing the translation of the operator in ACSL
	 */
	public String visitIncludesExcludesCall(
			OperationCallExp<Classifier, Operation> callExp, String oper) {
		OCLExpression<Classifier> source = callExp.getSource();
		String tab = source.accept(this) + "[i]";
		tab = maybePointerProperty(source, tab);
		String arg = callExp.getArgument().get(0).accept(this);
		Boolean includes = oper.equals("includes");
		String size = getSizeParamName(source);
		String ub = size + "-1";
		String quant = includes ? "\\exists" : "\\forall";
		String eq = includes ? " == " : " != ";
		String imp = includes ? " && " : " ==> ";
		String result = quant + " int i; 0 <= i <= " + ub + imp + tab + eq
				+ arg;
		return result;
	}

	/*
	 * Returns the name of the parameter that holds the size of the array or the
	 * macro name indicating the size if it is constant. For a parameter with
	 * multiplicity 0..* "a" it returns "size_a". For an array of constant size
	 * "a[MACRO_NAME]" it returns "MACRO_NAME" assuming the size is declared as
	 * a C macro. For a property call "obj.array" it returns the property
	 * "obj.size_array".
	 */
	@SuppressWarnings("unchecked")
	protected String getSizeParamName(OCLExpression<Classifier> array) {
		// Parameter
		if (array instanceof VariableExp) {
			Parameter param = (Parameter) ((VariableExp<Classifier, ?>) array)
					.getReferredVariable().getRepresentedParameter();
			if (param != null) {
				if (param.getUpper() == -1) {
					String size = "size_" + param.getName();
					return size;
				} else if (param.getLower() == param.getUpper()) {
					String size = param.getOperation().getName().toUpperCase()
							+ "_" + param.getName().toUpperCase() + "_SIZE";
					return size;
				}
			}

		}
		// Property
		if (array instanceof PropertyCallExp) {
			Property property = ((PropertyCallExp<Classifier, Property>) array)
					.getReferredProperty();
			if (property.getUpper() == -1) {
				String propertyName = property.getName();
				String tab = array.accept(this);
				String sizeProp = "size_" + propertyName;
				String size = tab.substring(0,
						tab.length() - propertyName.length())
						+ sizeProp;
				return size;
			} else if (property.getLower() == property.getUpper()) {
				String name = getNameOwner(property);
				String size = name + "_" + property.getName().toUpperCase()
						+ "_SIZE";
				return size;
			}
		}
		throw new IllegalArgumentException("Unhandled type of collection "
				+ array.getClass());
	}

	/*
	 * Returns the type of the object that owns this property. Returns the name
	 * of the datatype if the property belongs to a datatype, the name of the
	 * class if the property belongs to a class and the name of the member
	 * owning the property if part of an association
	 */
	private String getNameOwner(Property property) {
		String name = "";
		DataType type;
		org.eclipse.uml2.uml.Class c;
		if ((type = property.getDatatype()) != null) {
			name = type.getName().toUpperCase();
		} else if (property.getAssociation() != null) {
			name = property.getOtherEnd().getType().getName().toUpperCase();
		} else if ((c = property.getClass_()) != null) {
			name = c.getName().toUpperCase();
		}
		return name;
	}

	/**
	 * Visits a {@link VariableExp}.
	 * 
	 * @param v
	 *            The {@link VariableExp} to visit
	 * @return A String representing the translation of the variable in ACSL
	 */
	@Override
	public String visitVariableExp(VariableExp<Classifier, Parameter> v) {
		Variable<Classifier, Parameter> var = v.getReferredVariable();
		Parameter param = var.getRepresentedParameter();
		if (param != null) {
			if (param.getUpper() != 1)
				return v.getName();
			if (isPointer(param))
				return "*" + v.getName();
		}
		if (v.getName().equals("self")) return "*self";
		if (v.getName().equals("result")) {
			return "\\result";
		}
		return v.getName();
	}

	/*
	 * Checks if a parameter is a pointer
	 */
	private Boolean isPointer(Parameter param) {
		Type type = param.getType();
		Boolean isPrimitive = (type instanceof PrimitiveType);
		Boolean isEnum = (type instanceof Enumeration);
		return ((param.getDirection()
				.equals(ParameterDirectionKind.OUT_LITERAL) || param
				.getDirection().equals(ParameterDirectionKind.INOUT_LITERAL)) || (!isPrimitive && !isEnum));
	}

	/*
	 * Checks if a property is a pointer by checking if the property is a shared
	 * aggregation
	 */
	@SuppressWarnings("unchecked")
	protected String maybePointerProperty(OCLExpression<Classifier> exp,
			String base) {
		if (exp instanceof PropertyCallExp) {
			Property property = ((PropertyCallExp<Classifier, Property>) exp)
					.getReferredProperty();
			return property.getAggregation() == AggregationKind.SHARED_LITERAL ? "*("
					+ base + ")"
					: base;
		} else
			return base;
	}

	/**
	 * Visits an {@link IteratorExp}.
	 * <p>
	 * forAll, exists operators are implemented with the following restrictions
	 * on the source format:
	 * <p>
	 * <code>Sequence{i1..in}->iterator(i|f(a->at(i)))</code>
	 * <p>
	 * <code>a->iterator(x|f(x))</code> where a is a parameter of the operation
	 * of type array
	 * <p>
	 * <code>exp.ref->iterator(x|f(x))</code> where ref is an array property of
	 * the type of the expression
	 * <p>
	 * <code>a -> one( x | f(x) )</code> generates the following ACSL contract :
	 * <code>(\exists int i; 0 <= i <= size_a-1 && f(a[i])) && (\forall int j; 0 <= j <= size_a-1 && j!=i ==> !f(a[j]))</code>
	 * 
	 * @param callExp
	 *            The {@link IteratorExp} to visit
	 * @return A string representing the corresponding ACSL contract
	 */
	@Override
	public String visitIteratorExp(IteratorExp<Classifier, Parameter> callExp) {
		if (callExp.getName().equals("forAll")) {
			return visitIteratorExp(callExp, "forall");
		}
		if (callExp.getName().equals("exists")) {
			return visitIteratorExp(callExp, "exists");
		}
		if (callExp.getName().equals("one")) {
			return visitOneCall(callExp);
		}
		return "IteratorExp";
	}

	/*
	 * Visits forall/exists iterators, checks the type of the source and
	 * generates the corresponding contract
	 */
	private String visitIteratorExp(IteratorExp<Classifier, Parameter> callExp,
			String type) {
		String result = "";
		OCLExpression<Classifier> source = callExp.getSource();
		// Sequence of indices
		if (source instanceof CollectionLiteralExp
				&& ((CollectionLiteralExp<Classifier>) source).getKind() == CollectionKind.SEQUENCE_LITERAL) {
			EList<CollectionLiteralPart<Classifier>> parts = ((CollectionLiteralExp<Classifier>) source)
					.getPart();
			int nbParts = parts.size();
			if (nbParts == 1) {
				CollectionLiteralPart<Classifier> part = parts.get(0);
				if (part instanceof CollectionRange) {
					String min_index = ((CollectionRange<Classifier>) part)
							.getFirst().accept(this);
					String max_index = ((CollectionRange<Classifier>) part)
							.getLast().accept(this);
					result = generateIteratorExpression(type,
							callExp.getIterator(), min_index, max_index,
							callExp.getBody(), null);
					return result;
				}
			}
		}
		// Array (Parameter or property)
		String min_index = "0";
		String max_index = getSizeParamName(source) + "-1";
		result = generateIteratorExpression(type, callExp.getIterator(),
				min_index, max_index, callExp.getBody(), source);
		return result;
	}

	/*
	 * Generates the ACSL contract for the given iterator with the given bounds
	 * on indices and the given body
	 */
	private String generateIteratorExpression(String type,
			EList<Variable<Classifier, Parameter>> iterator, String min_index,
			String max_index, OCLExpression<Classifier> body,
			OCLExpression<Classifier> source) {
		String result = "\\" + type + " ";
		String variables = "";
		String intervals = "";
		int nbVars = iterator.size();
		String bodyExp = body.accept(this);
		Boolean hasSource = (source != null);
		for (Variable<Classifier, Parameter> var : iterator) {
			String name = var.getName();
			String it = hasSource ? "it_" + name : name;
			variables += "int " + it;
			intervals += min_index + " <= " + it + " <= " + max_index;
			if (iterator.indexOf(var) != nbVars - 1) {
				variables += ", ";
				intervals += " && ";
			}
			if (hasSource) {
				String array = source.accept(this) + "[" + it + "]";
				array = maybePointerProperty(source, array);
				bodyExp = "\\let " + name + "=" + array + ";(" + bodyExp + ")";
			}
		}
		Boolean forall = type.equals("forall");
		String imp = forall ? " ==> " : " && ";
		result += variables + "; (" + intervals + ")" + imp + bodyExp;
		return result;
	}

	/*
	 * Generates the contract for the ONE iterator
	 */
	private String visitOneCall(IteratorExp<Classifier, Parameter> callExp) {
		OCLExpression<Classifier> array = callExp.getSource();
		OCLExpression<Classifier> body = callExp.getBody();
		EList<Variable<Classifier, Parameter>> iterator = callExp.getIterator();
		String varName = iterator.get(0).getName();
		String tab = array.accept(this);
		String exp = body.accept(this);
		String tabi = maybePointerProperty(array, tab + "[i]");
		String tabj = maybePointerProperty(array, tab + "[j]");
		String expi = "\\let " + varName + "=" + tabi + ";(" + exp + ")";
		String expj = "\\let " + varName + "=" + tabj + ";(" + exp + ")";
		String size = getSizeParamName(array);
		String ub = size + "-1";
		String exists = "\\exists int i; (0<=i<=" + ub + " && " + expi + " && ";
		String forall = "(\\forall int j; (0<=j<=" + ub + " && j!=i) ==> !("
				+ expj + ")))";
		return exists + forall;
	}

	/**
	 * Visits an {@link IfExp}.
	 * <p>
	 * <code> if condition then exp1 else exp2 endif </code> is directly
	 * translated to the ACSL conditional expression
	 * <code>condition?exp1:exp2</code>
	 * 
	 * @param ifExp
	 *            The {@link IfExp} to visit
	 * @return A String representing the conditional in ACSL
	 */
	@Override
	public String visitIfExp(IfExp<Classifier> ifExp) {
		String cond = ifExp.getCondition().accept(this);
		String thenExp = ifExp.getThenExpression().accept(this);
		String elseExp = ifExp.getElseExpression().accept(this);
		return cond + "?" + thenExp + ":" + elseExp;
	}

	/**
	 * Visits a {@link LetExp}.
	 * <p>
	 * <code>let id : type = exp in body</code> is directly tranlated to
	 * <code>\let id = exp; body</code>
	 * 
	 * @param letExp
	 *            The {@link LetExp} to visit
	 * @return A string corresponding to the ACSL let operator
	 */
	@Override
	public String visitLetExp(LetExp<Classifier, Parameter> letExp) {
		String var = letExp.getVariable().getName();
		String exp = letExp.getVariable().getInitExpression().accept(this);
		String inExp = letExp.getIn().accept(this);
		return "\\let " + var + "=" + exp + ";" + inExp;
	}

	/**
	 * Visits an {@link IntegerLiteralExp}.
	 * 
	 * @param literalExp
	 *            The {@link IntegerLiteralExp} to visit
	 * @return The string representation of the integer
	 */
	@Override
	public String visitIntegerLiteralExp(
			IntegerLiteralExp<Classifier> literalExp) {
		return literalExp.getIntegerSymbol().toString();
	}

	/**
	 * Visits an {@link UnlimitedNaturalLiteralExp}.
	 * 
	 * @param literalExp
	 *            The {@link UnlimitedNaturalLiteralExp} to visit
	 * @return The string representation of the unlimited integer
	 */
	@Override
	public String visitUnlimitedNaturalLiteralExp(
			UnlimitedNaturalLiteralExp<Classifier> literalExp) {
		return literalExp.getIntegerSymbol().toString();
	}

	/**
	 * Visits a {@link RealLiteralExp}.
	 * 
	 * @param literalExp
	 *            The {@link RealLiteralExp} to visit
	 * @return The string representation of the real
	 */
	@Override
	public String visitRealLiteralExp(RealLiteralExp<Classifier> literalExp) {
		return literalExp.getRealSymbol().toString();
	}

	/**
	 * Visits a {@link StringLiteralExp}.
	 * 
	 * @param literalExp
	 *            The {@link StringLiteralExp} to visit
	 * @return The string representation of the string
	 */
	@Override
	public String visitStringLiteralExp(StringLiteralExp<Classifier> literalExp) {
		return literalExp.getStringSymbol();
	}

	/**
	 * Visits a {@link BooleanLiteralExp}.
	 * 
	 * @param literalExp
	 *            The {@link BooleanLiteralExp} to visit
	 * @return A String representing the ACSL booleans : \true or \false
	 */
	@Override
	public String visitBooleanLiteralExp(
			BooleanLiteralExp<Classifier> literalExp) {
		return "\\" + literalExp.getBooleanSymbol().toString();
	}

	/**
	 * Visits a {@link NullLiteralExp}.
	 * 
	 * @param literalExp
	 *            The {@link NullLiteralExp} to visit
	 * @return A String representing the ACSL null notation : \null
	 */
	@Override
	public String visitNullLiteralExp(NullLiteralExp<Classifier> literalExp) {
		return "\\null";
	}
	
	@Override
	public String visitCollectionItem(CollectionItem<Classifier> item) {
		return item.getItem().accept(this);
	}
	
	/**
	 * Not implemented
	 */
	@Override
	public String visitEnumLiteralExp(
			EnumLiteralExp<Classifier, EnumerationLiteral> literalExp) {
		EnumerationLiteral enumLiteral = literalExp.getReferredEnumLiteral();
		
		return enumLiteral.getName();
	}

	@Override
	public String visitExpressionInOCL(
			ExpressionInOCL<Classifier, Parameter> expression) {
		return expression.getBodyExpression().accept(this);
	}


	/**
	 * Not implemented
	 */
	@Override
	public String visitConstraint(Constraint constraint) {
		return "constraint";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitAssociationClassCallExp(
			AssociationClassCallExp<Classifier, Property> callExp) {
		return "AssociationClassCallExp";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitVariable(Variable<Classifier, Parameter> variable) {
		return "Variable";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitTypeExp(TypeExp<Classifier> t) {
		return "";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitMessageExp(
			MessageExp<Classifier, CallOperationAction, SendSignalAction> messageExp) {
		return "MessageExp";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitUnspecifiedValueExp(
			UnspecifiedValueExp<Classifier> unspecExp) {
		return "UnspecifiedValueExp";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitStateExp(StateExp<Classifier, State> stateExp) {
		return "StateExp";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitInvalidLiteralExp(
			InvalidLiteralExp<Classifier> literalExp) {
		return "InvalidLiteralExp";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitTupleLiteralExp(
			TupleLiteralExp<Classifier, Property> literalExp) {
		return "TupleLiteralExp";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitTupleLiteralPart(
			TupleLiteralPart<Classifier, Property> part) {
		return "TupleLiteralPart";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitCollectionLiteralExp(
			CollectionLiteralExp<Classifier> literalExp) {
		return "CollectionLiteralExp";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitCollectionRange(CollectionRange<Classifier> range) {
		return "CollectionRange";
	}

	/**
	 * Not implemented
	 */
	@Override
	public String visitIterateExp(IterateExp<Classifier, Parameter> callExp) {
		return "IterateExp";
	}

}
