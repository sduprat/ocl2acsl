package org.eclipse.ocl2acsl;

import java.util.LinkedList;
import java.util.List;

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
import org.eclipse.uml2.uml.Property;


public class Ocl2acsl {

    protected  OCL<?, Classifier, Operation, Property, ?, ?, ?, ?, ?, ?, ?, ?> ocl;
    protected  UMLEnvironmentFactory envFact;
    protected  OCLHelper<Classifier, Operation, Property,Constraint> helper;	
    protected static String EXT_ID = "customOperation" ; 
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
				result.add(op);
			} catch (CoreException e) {
				e.printStackTrace();
			}
			
		}
		return result;
	}

	public  String prepost2acsl (Constraint cons) throws OCL2acslParserException{
		
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
	
	public  String inv2acsl (Constraint cons)throws OCL2acslParserException{
		
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
 }
