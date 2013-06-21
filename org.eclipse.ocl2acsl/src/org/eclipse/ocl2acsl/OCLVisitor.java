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


import org.eclipse.ocl.expressions.AssociationClassCallExp;
import org.eclipse.ocl.expressions.BooleanLiteralExp;
import org.eclipse.ocl.expressions.CollectionItem;
import org.eclipse.ocl.expressions.CollectionLiteralExp;
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
import org.eclipse.ocl.uml.impl.CollectionLiteralExpImpl;
import org.eclipse.ocl.uml.impl.SequenceTypeImpl;
import org.eclipse.ocl.uml.impl.VariableExpImpl;
import org.eclipse.ocl.utilities.AbstractVisitor;
import org.eclipse.ocl.utilities.ExpressionInOCL;
import org.eclipse.uml2.uml.CallOperationAction;
import org.eclipse.uml2.uml.Classifier;
import org.eclipse.uml2.uml.Constraint;
import org.eclipse.uml2.uml.EnumerationLiteral;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Parameter;
import org.eclipse.uml2.uml.ParameterDirectionKind;
import org.eclipse.uml2.uml.Property;
import org.eclipse.uml2.uml.SendSignalAction;
import org.eclipse.uml2.uml.State;

public class OCLVisitor extends
		AbstractVisitor<String, Classifier, Operation, Property, EnumerationLiteral, Parameter, State, CallOperationAction, SendSignalAction, Constraint> {

	@Override
	public String visitPropertyCallExp(
			PropertyCallExp<Classifier, Property> callExp) {
		return maybeAtPre(callExp, callExp.getReferredProperty().getName());
	}

	@Override
	public String visitBooleanLiteralExp(
			BooleanLiteralExp<Classifier> literalExp) {
		return literalExp.getBooleanSymbol().toString();
	}

	@Override
	public String visitNullLiteralExp(NullLiteralExp<Classifier> literalExp) {
		return "null";
	}

	@Override
	public String visitConstraint(Constraint constraint) {
		System.out.println(constraint);
		return "constraint";
	}

	@Override
	public String visitOperationCallExp(
			OperationCallExp<Classifier, Operation> callExp) {
		
		String oper = ocl2acslOperator(callExp.getReferredOperation().getName());
		
		if (oper.equals("first")){
			String op1 = callExp.getSource().accept(this);
			return op1 + "[0]" ;
		}
		if (oper.equals("at")){
			String op1 = callExp.getSource().accept(this);
			String op2 = callExp.getArgument().get(0).accept(this);
			return op1 + "["+ op2 +"]" ;
		}
		if (isUnaryOperator(callExp)){
			String op1 = callExp.getSource().accept(this);
			if (needParenthesis(callExp.getSource(), oper)){
				op1 = "(" + op1 + ")";
			}
			if (oper.equals("-") || oper.equals("!")){
				return  oper + op1 ;
			} else {
				return "\\"+ oper + "(" + op1 + ")" ;
			}
		}
		if (isBynaryOperator(callExp)){
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
			 		return "\\"+ oper + "(" + op1 + ", " + op2 +")" ;
			 	}
		}
		return "operator " + oper + " not supported";
		}
	
	private boolean isInfix (String oper){
		return oper.equals("*") || oper.equals("/") || oper.equals("+") || oper.equals("-") || oper.equals("<") || oper.equals(">") || oper.equals("<=") ||
				oper.equals(">=") || oper.equals("==") || oper.equals("<>") || oper.equals("||") || oper.equals("^^") || oper.equals("&&") ||
				oper.equals("==>") || oper.equals("%");
	}
	
	
	private boolean isBynaryOperator(
			OperationCallExp<Classifier, Operation> callExp) {
		return (callExp.getArgument().size() == 1);
	}

	private boolean isUnaryOperator(
			OperationCallExp<Classifier, Operation> callExp) {
		return (callExp.getArgument().size() == 0);
	}


	private String ocl2acslOperator(String oper) {
		if (oper.equals("=")) return "==";
		if (oper.equals("or")) return "||";
		if (oper.equals("xor")) return "^^";
		if (oper.equals("and")) return "&&";
		if (oper.equals("not")) return "!";
		if (oper.equals("implies")) return "==>";
		if (oper.equals("div")) return "/";
		if (oper.equals("mod")) return "%";
		if (oper.equals("round")) return "ceil";
		return oper;
	}

	private boolean needParenthesis(OCLExpression<Classifier> exp, String oper){
		if (exp instanceof OperationCallExp){
			String op2 = ocl2acslOperator(((OperationCallExp<Classifier, Operation>) exp).getReferredOperation().getName());
			if (getPriority(op2) < getPriority(oper)) return true ;
		}
		return false ;
	}
	
	private int getPriority(String oper){
		if (oper.equals("at") || oper.equals("first")) return 110 ;
		if (oper.equals("*") || oper.equals("/") || oper.equals("%")) return 100 ;
		if (oper.equals("+") || oper.equals("-")) return 90 ;
		if (oper.equals(">") || oper.equals("<") || oper.equals(">=") || oper.equals("<=")) return 80 ;
		if (oper.equals("==") || oper.equals("<>")) return 70 ;
		if (oper.equals("&&")) return 60 ;
		if (oper.equals("||")) return 50 ;
		if (oper.equals("^^")) return 40 ;
		if (oper.equals("==>")) return 30 ;
		return 120 ;
	}
	
	@Override
	public String visitVariableExp(VariableExp<Classifier, Parameter> v) {
		if (v.getReferredVariable().getRepresentedParameter() != null){
		if (v.getReferredVariable().getRepresentedParameter().getDirection().equals(ParameterDirectionKind.OUT_LITERAL)
			|| v.getReferredVariable().getRepresentedParameter().getDirection().equals(ParameterDirectionKind.INOUT_LITERAL)){
			return "*" + v.getName();
		}}
		if (v.getName().equals("result")){
			return "\\result";
		}
		return v.getName();
	}

	@Override
	public String visitAssociationClassCallExp(
			AssociationClassCallExp<Classifier, Property> callExp) {
		return "AssociationClassCallExp";
	}

	@Override
	public String visitVariable(Variable<Classifier, Parameter> variable) {
		return "Variable";
	}

	@Override
	public String visitIfExp(IfExp<Classifier> ifExp) {
		return "IfExp";
	}

	@Override
	public String visitTypeExp(TypeExp<Classifier> t) {
		return "TypeExp";
	}

	@Override
	public String visitMessageExp(
			MessageExp<Classifier, CallOperationAction, SendSignalAction> messageExp) {
		return "MessageExp";
	}

	@Override
	public String visitUnspecifiedValueExp(
			UnspecifiedValueExp<Classifier> unspecExp) {
		return "UnspecifiedValueExp";
	}

	@Override
	public String visitStateExp(StateExp<Classifier, State> stateExp) {
		return "StateExp";
	}

	@Override
	public String visitIntegerLiteralExp(
			IntegerLiteralExp<Classifier> literalExp) {
		return literalExp.getIntegerSymbol().toString();
	}

	@Override
	public String visitUnlimitedNaturalLiteralExp(
			UnlimitedNaturalLiteralExp<Classifier> literalExp) {
		return literalExp.getIntegerSymbol().toString() ;
	}

	@Override
	public String visitRealLiteralExp(RealLiteralExp<Classifier> literalExp) {
		return literalExp.getRealSymbol().toString();
	}

	@Override
	public String visitStringLiteralExp(StringLiteralExp<Classifier> literalExp) {
		return literalExp.getStringSymbol();
	}

	@Override
	public String visitInvalidLiteralExp(
			InvalidLiteralExp<Classifier> literalExp) {
		return "InvalidLiteralExp";
	}

	@Override
	public String visitTupleLiteralExp(
			TupleLiteralExp<Classifier, Property> literalExp) {
		return "TupleLiteralExp";
	}

	@Override
	public String visitTupleLiteralPart(
			TupleLiteralPart<Classifier, Property> part) {
		return "TupleLiteralPart";
	}

	@Override
	public String visitLetExp(LetExp<Classifier, Parameter> letExp) {
		return "LetExp";
	}

	@Override
	public String visitEnumLiteralExp(
			EnumLiteralExp<Classifier, EnumerationLiteral> literalExp) {
		return "EnumLiteralExp";
	}

	@Override
	public String visitCollectionLiteralExp(
			CollectionLiteralExp<Classifier> literalExp) {
		return "CollectionLiteralExp";
	}

	@Override
	public String visitCollectionItem(CollectionItem<Classifier> item) {
		return "CollectionItem";
	}

	@Override
	public String visitCollectionRange(CollectionRange<Classifier> range) {
		return "CollectionRange";
	}

	@Override
	public String visitIteratorExp(IteratorExp<Classifier, Parameter> callExp) {
		String result = "";
		if (callExp.getName().equals("forAll")){
			String max_index = "" ;
			if (callExp.getSource() instanceof VariableExpImpl){
				max_index = ((VariableExpImpl)callExp.getSource()).getReferredVariable().getRepresentedParameter().getUpper() + "" ;
			}
			//cas de l'attribut 
			if (callExp.getSource() instanceof PropertyCallExp){
				max_index = ((Property)((PropertyCallExp)callExp.getSource()).getReferredProperty()).getUpper() + ""  ;
			}

			String it = callExp.getIterator().get(0).getName();
			String tab_name = callExp.getSource().accept(this) ;
			String index_name = "index_" + tab_name ;
			String bool_exp = callExp.getBody().accept(this);
			if (callExp.getSource() instanceof CollectionLiteralExpImpl){
				if (((CollectionLiteralExpImpl)callExp.getSource()).getPart().get(0) instanceof CollectionRange){
					CollectionRange col = (CollectionRange) ((CollectionLiteralExpImpl)callExp.getSource()).getPart().get(0);
					max_index = col.getLast().accept(this) ;
					result = "\\forall int " + it + " ; " + col.getFirst().accept(this) + " <= " + it + " < " + max_index + " ==> " + bool_exp;
					return result ;
				}
			}
			bool_exp = bool_exp.replaceAll(it, tab_name+"[" + index_name+ "]") ;
			result = "\\forall int " + index_name + " ; 0 <= " + index_name + " < " + max_index; 
			
			if (callExp.getIterator().size() > 1){
				String it2 = callExp.getIterator().get(1).getName();
				String index2_name = "index2_" + tab_name ;
				result = "\\forall int " + index_name + ", int " + index2_name + " ; 0 <= " + index_name + " < " + max_index + " && 0 <= " + index2_name + " < " + max_index; 
				bool_exp = bool_exp.replaceAll(it2, tab_name+"[" + index2_name + "]") ;
			}
			result = result + " ==> " + bool_exp ;
			return result ;
		}
		if (callExp.getName().equals("exists")){
			int max_index = 0 ;
			if (callExp.getSource() instanceof VariableExpImpl){
				max_index = ((VariableExpImpl)callExp.getSource()).getReferredVariable().getRepresentedParameter().getUpper() ;
			}
			//cas de l'attribut
			if (callExp.getSource() instanceof PropertyCallExp){
				max_index = ((Property)((PropertyCallExp)callExp.getSource()).getReferredProperty()).getUpper() ;
			}
			String it = callExp.getIterator().get(0).getName();
			String tab_name = callExp.getSource().accept(this) ;
			String index_name = "index_" + tab_name ;
			String bool_exp = callExp.getBody().accept(this);
			if (callExp.getSource() instanceof CollectionLiteralExpImpl){
				if (((CollectionLiteralExpImpl)callExp.getSource()).getPart().get(0) instanceof CollectionRange){
					CollectionRange col = (CollectionRange) ((CollectionLiteralExpImpl)callExp.getSource()).getPart().get(0);
					String max_indexs = col.getLast().accept(this) ;
					result = "\\exists int " + it + " ; " + col.getFirst().accept(this) + " <= " + it + " < " + max_indexs + " && " + bool_exp;
					return result ;
				}
			}
			
			bool_exp = bool_exp.replaceAll(it, tab_name+"[" + index_name+ "]") ;
			result = "\\exists int " + index_name + " ; 0 <= " + index_name + " < " + max_index; 
			
			if (callExp.getIterator().size() > 1){
				String it2 = callExp.getIterator().get(1).getName();
				String index2_name = "index2_" + tab_name ;
				result = "\\exists int " + index_name + ", int " + index2_name + " ; 0 <= " + index_name + " < " + max_index + " && 0 <= " + index2_name + " < " + max_index; 
				bool_exp = bool_exp.replaceAll(it2, tab_name+"[" + index2_name + "]") ;
			}
			
			result = result + " && " + bool_exp ;
			return result ;
		}
		return "IteratorExp";
	}

	@Override
	public String visitIterateExp(IterateExp<Classifier, Parameter> callExp) {
		return "IterateExp";
	}

	@Override
	public String visitExpressionInOCL(
			ExpressionInOCL<Classifier, Parameter> expression) {
		return expression.getBodyExpression().accept(this);
	}

	private String maybeAtPre(FeatureCallExp mpc, String base) {
		return mpc.isMarkedPre() ? "\\old("+base + ")" : base;
	}
	

	
}
