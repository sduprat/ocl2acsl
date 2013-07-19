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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ArrayList;
import org.eclipse.emf.common.util.EList;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.eclipse.ocl.OCL;
import org.eclipse.ocl.ParserException;
import org.eclipse.ocl.helper.OCLHelper;
import org.eclipse.ocl.uml.ExpressionInOCL;
import org.eclipse.ocl.uml.UMLEnvironment;
import org.eclipse.ocl.uml.UMLEnvironmentFactory;
import org.eclipse.ocl2acsl.additionalOperations.CustomOperation;
import org.eclipse.uml2.uml.Classifier;
import org.eclipse.uml2.uml.Constraint;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Parameter;
import org.eclipse.uml2.uml.PrimitiveType;
import org.eclipse.uml2.uml.Property;

/**
 * Ocl2acsl provides the environment for ACSL code generation from OCL
 * constraints.
 * 
 * @author A560169
 * 
 */
public class Ocl2acsl {

    protected  OCL<?, Classifier, Operation, Property, ?, ?, ?, ?, ?, ?, ?, ?> ocl;
    protected  UMLEnvironmentFactory envFact;
    protected  OCLHelper<Classifier, Operation, Property,Constraint> helper;	
    protected static String EXT_ID = "customOperation" ; 
    protected static HashMap<String, String> acslOperationName = new HashMap<String, String>() ;
    protected static HashMap<String, String> acslOperationNotationType = new HashMap<String, String>() ;
    protected static List<CustomOperation> allOperations = getAllOperations();
    
    
	public Ocl2acsl() {
		//initialization of the environment
		envFact = new UMLEnvironmentFactory();
		ocl = OCL.newInstance(envFact );
		helper = (OCLHelper<Classifier, Operation, Property, Constraint>) ocl.createOCLHelper();
		for (CustomOperation c : allOperations){
			addOperationToEnvironment(c);
		}
		//definition of new acsl operation
	}
	
	private static List<CustomOperation> getAllOperations() {
		List<CustomOperation> result = new LinkedList<CustomOperation>();
		IConfigurationElement[] extensions = Platform.getExtensionRegistry().getConfigurationElementsFor(Activator.PLUGIN_ID, EXT_ID);
		for (IConfigurationElement c : extensions){
			try {
				CustomOperation op = (CustomOperation) c.createExecutableExtension("instance");
				acslOperationName.put(op.getName(), c.getAttribute("acslName"));
				acslOperationNotationType.put(c.getAttribute("acslName"), c.getAttribute("notation_type"));
				result.add(op);
			} catch (CoreException e) {
				e.printStackTrace();
			}
			
		}
		return result;
	}

	/**
	 * Generates the ACSL contract corresponding to the given OCL pre/post
	 * condition
	 * 
	 * @param cons
	 *            The constraint to translate
	 * @return A string representing the ACSL contract
	 * @throws OCL2acslParserException
	 *             Thrown if the OCL parser fails to parse the constraint
	 */
	public String prepost2acsl(Constraint cons) throws OCL2acslParserException {

		String result = "";
		Operation context = (Operation) cons.getContext() ;
		String constraint = cons.getSpecification().stringValue();

		
		helper.setOperationContext(context.getClass_(), context);
		try {
			Constraint c_ocl = helper.createPostcondition(constraint);
			if (c_ocl.getSpecification()  instanceof ExpressionInOCL) {
				ExpressionInOCL expInOCl = (ExpressionInOCL) c_ocl.getSpecification() ;
				OCLVisitor visitorVenuDAilleurs = new OCLVisitor();
				result = expInOCl.accept(visitorVenuDAilleurs);
			}
		} catch (ParserException e) {
			e.printStackTrace();
			throw new OCL2acslParserException(e);
		}
		
		return result ;
	}

	/**
	 * Generates the ACSL contract corresponding to the given OCL invariant
	 * 
	 * @param cons
	 *            The constraint to translate
	 * @return A string representing the ACSL contract
	 * @throws OCL2acslParserException
	 *             Thrown if the OCL parser fails to parse the constraint
	 */
	public String inv2acsl(Constraint cons) throws OCL2acslParserException {

		String result = "";
		Classifier context = (Classifier) cons.getContext() ;
		String constraint = cons.getSpecification().stringValue();

		helper.setContext(context);
		
		try {
			Constraint c_ocl = helper.createInvariant(constraint);
			if (c_ocl.getSpecification()  instanceof ExpressionInOCL) {
				ExpressionInOCL expInOCl = (ExpressionInOCL) c_ocl.getSpecification() ;
				OCLVisitor visitorVenuDAilleurs = new OCLVisitor();
				result = expInOCl.accept(visitorVenuDAilleurs);
			}
		} catch (ParserException e) {
			throw new OCL2acslParserException(e);
		}
		
		return result ;
	}

    private  void addOperationToEnvironment(CustomOperation operation) {
        if(operation != null && operation.getName() != null && !operation.getName().isEmpty()) {           
        		UMLEnvironment umlEnvironment = (UMLEnvironment) ocl.getEnvironment();
        		umlEnvironment.defineOperation(operation.getClassifier(), operation.getName(), operation.getType(), operation.getParameters(), org.eclipse.uml2.uml.UMLFactory.eINSTANCE.createConstraint());
        }
    }

	/**
	 * Returns a list of ACSL valid clauses corresponding to the pointers
	 * introduced to represent modifiable parameters
	 * 
	 * @param op
	 *            The {@link Operation} for which we are generating the valid
	 *            clauses
	 * @return A list of strings representing the different valid clauses
	 */
	public ArrayList<String> generateValidClauses(Operation op) {
		EList<Parameter> params = op.getOwnedParameters();
		ArrayList<String> validClauses = new ArrayList<String>();
		for (Parameter p : params) {
			String direction = p.getDirection().toString();
			Boolean isPrimitive = p.getType() instanceof PrimitiveType;
			// User-defined objects and out/inout primitive type params that are
			// not collections
			if ((direction.equals("out") || direction.equals("inout") || !isPrimitive)
					&& p.getUpper() == 1) {
				String clause = "\\valid(" + p.getName() + ")";
				validClauses.add(clause);
			}
		}
		if (!op.isStatic()) {
			String clause = "\\valid(self)";
			validClauses.add(clause);
		}
		return validClauses;
	}

	/**
	 * Returns a list of parameters variables corresponding to the parameters
	 * the operation can modify
	 * 
	 * @param op
	 *            The {@link Operation} considered
	 * @return A list of strings representing the parameters
	 */
	public ArrayList<String> getAssignedParameters(Operation op) {
		EList<Parameter> params = op.getOwnedParameters();
		ArrayList<String> assigned = new ArrayList<String>();
		for (Parameter p : params) {
			String effect = p.getEffect().toString();
			String direction = p.getDirection().toString();
			String param;
			// Effects that allow modification
			if ((effect.equals("create") || effect.equals("delete") || effect
					.equals("update")) && !direction.equals("return")) {
				// Pointers = All user-defined objects and out/inout primitive
				// type params
				if (p.getUpper() == 1) {
					Boolean isPrimitive = p.getType() instanceof PrimitiveType;
					if (!isPrimitive || !direction.equals("in")) {
						param = "*" + p.getName();
						assigned.add(param);
					}
					// Array of undefined size
				} else if (p.getUpper() == -1) {
					param = p.getName() + "[0..size_" + p.getName() + "-1]";
					assigned.add(param);
					// Arrays of constant size
				} else {
					String size = op.getName().toUpperCase() + "_"
							+ p.getName().toUpperCase() + "_SIZE";
					param = p.getName() + "[0.. " + size + " -1]";
					assigned.add(param);
				}
			}
		}
		if (!op.isStatic()) {
			assigned.add("*self");
		}
		return assigned;
	}

	/**
	 * Returns a list of ACSL valid clauses corresponding to the arrays
	 * manipulated by the operation
	 * 
	 * @param op
	 *            The {@link Operation} for which we are generating the valid
	 *            clauses
	 * @return A list of strings representing the different valid clauses
	 */
	public ArrayList<String> generateArrayValidClauses(Operation op) {
		EList<Parameter> params = op.getOwnedParameters();
		ArrayList<String> validClauses = new ArrayList<String>();
		for (Parameter p : params) {
			// Arrays of undefined size
			if (p.getUpper() == -1) {
				String name = p.getName();
				String clause = "\\valid(" + name + "+(0..size_" + name
						+ "-1)) && size_" + name + ">=0";
				validClauses.add(clause);
				// Arrays of constant size
			} else if (p.getUpper() != 1) {
				String name = p.getName();
				String size = op.getName().toUpperCase() + "_"
						+ p.getName().toUpperCase() + "_SIZE";
				String clause = "\\valid(" + name + "+(0.. " + size
						+ " -1)) && " + size + " >=0";
				validClauses.add(clause);
			}
		}
		return validClauses;
	}

}
