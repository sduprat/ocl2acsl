package additionalOperations;

import java.util.List;
import org.eclipse.ocl.expressions.Variable ;
import org.eclipse.uml2.uml.Classifier;
import org.eclipse.uml2.uml.Parameter;

public interface CustomOperation {

	
    public List<Variable<Classifier, Parameter>> getParameters() ;
    public Classifier getType() ;
    public Classifier getClassifier()  ;
    public String getName() ;
}
