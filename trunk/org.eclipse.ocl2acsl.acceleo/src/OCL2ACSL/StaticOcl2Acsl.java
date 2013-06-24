package OCL2ACSL;

import java.util.ArrayList;

import org.eclipse.ocl2acsl.OCL2acslParserException;
import org.eclipse.ocl2acsl.Ocl2acsl;
import org.eclipse.uml2.uml.Constraint;
import org.eclipse.uml2.uml.Operation;

public class StaticOcl2Acsl {

	public static Ocl2acsl ocl2acsl = new Ocl2acsl();

	public static String prepost2acsl(Constraint cons) {
		try {
			return ocl2acsl.prepost2acsl(cons);
		} catch (OCL2acslParserException e) {
			return e.getMessage();
		} catch (IllegalArgumentException e) {
			return e.getMessage();
		}
	}

	public static String inv2acsl(Constraint cons) {
		try {
			return ocl2acsl.inv2acsl(cons);
		} catch (OCL2acslParserException e) {
			return e.getMessage();
		} catch (IllegalArgumentException e) {
			return e.getMessage();
		}
	}

	public static ArrayList<String> generateValidClauses(Operation op) {
		return ocl2acsl.generateValidClauses(op);
	}

	public static ArrayList<String> getAssignedParameters(Operation op) {
		return ocl2acsl.getAssignedParameters(op);
	}

	public static ArrayList<String> generateArrayValidClauses(Operation op) {
		return ocl2acsl.generateArrayValidClauses(op);
	}

}