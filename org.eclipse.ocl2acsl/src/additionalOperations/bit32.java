package additionalOperations;

import java.util.Collections;
import java.util.List;

import org.eclipse.ocl.expressions.ExpressionsFactory;
import org.eclipse.ocl.expressions.Variable;
import org.eclipse.uml2.uml.Classifier;
import org.eclipse.uml2.uml.Parameter;
import org.eclipse.ocl.uml.internal.OCLStandardLibraryImpl;


public class bit32 implements CustomOperation {

	@Override
	public List<Variable<Classifier, Parameter>> getParameters() {
		Variable<Classifier, Parameter> var = ExpressionsFactory.eINSTANCE.createVariable();
        var.setName("n_bit");
        var.setType(OCLStandardLibraryImpl.INSTANCE.getInteger());
        return Collections.singletonList(var);
	}

	@Override
	public Classifier getType() {
		return OCLStandardLibraryImpl.INSTANCE.getBoolean();
	}

	@Override
	public Classifier getClassifier() {
		return OCLStandardLibraryImpl.INSTANCE.getInteger();
	}

	@Override
	public String getName() {
		return "bit32";
	}

}
