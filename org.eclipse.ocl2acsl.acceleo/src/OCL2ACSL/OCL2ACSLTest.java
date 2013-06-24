package OCL2ACSL;

import java.util.Iterator;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.papyrus.sysml.activities.ActivitiesPackage;
import org.eclipse.papyrus.sysml.allocations.AllocationsPackage;
import org.eclipse.papyrus.sysml.blocks.BlocksPackage;
import org.eclipse.papyrus.sysml.constraints.ConstraintsPackage;
import org.eclipse.papyrus.sysml.interactions.InteractionsPackage;
import org.eclipse.papyrus.sysml.portandflows.PortandflowsPackage;
import org.eclipse.papyrus.sysml.requirements.RequirementsPackage;
import org.eclipse.uml2.uml.Constraint;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.UMLPackage;
import org.eclipse.uml2.uml.resource.UMLResource;
import org.eclipse.uml2.uml.util.UMLSwitch;

// Java class to test the translation 
public class OCL2ACSLTest {

	private static URI PLUGIN_PATH = URI
			.createURI("jar:file:/D:/Topcased-5.3.0/plugins/org.eclipse.uml2.uml.resources_3.1.100.v201008191510.jar!/libraries/");

	public static void testOcl2ACSL() {
		final ResourceSet resourceSet = new ResourceSetImpl();
		resourceSet.getResourceFactoryRegistry().getExtensionToFactoryMap()
				.put(UMLResource.FILE_EXTENSION, UMLResource.Factory.INSTANCE);
		resourceSet.getPackageRegistry().put(UMLPackage.eNS_URI,
				UMLPackage.eINSTANCE);
		resourceSet.getPackageRegistry().put(BlocksPackage.eNS_URI,
				BlocksPackage.eINSTANCE);
		resourceSet.getPackageRegistry().put(RequirementsPackage.eNS_URI,
				RequirementsPackage.eINSTANCE);
		resourceSet.getPackageRegistry().put(AllocationsPackage.eNS_URI,
				AllocationsPackage.eINSTANCE);
		resourceSet.getPackageRegistry().put(ActivitiesPackage.eNS_URI,
				ActivitiesPackage.eINSTANCE);
		resourceSet.getPackageRegistry().put(PortandflowsPackage.eNS_URI,
				PortandflowsPackage.eINSTANCE);
		resourceSet.getPackageRegistry().put(ConstraintsPackage.eNS_URI,
				ConstraintsPackage.eINSTANCE);
		resourceSet.getPackageRegistry().put(InteractionsPackage.eNS_URI,
				InteractionsPackage.eINSTANCE);
		resourceSet.getPackageRegistry().put(BlocksPackage.eNS_URI,
				BlocksPackage.eINSTANCE);
		resourceSet.getURIConverter().getURIMap()
				.put(URI.createURI("pathmap://UML_LIBRARIES/"), PLUGIN_PATH);

		String model1 = "D:\\documents\\A560169\\workspace\\ActivityDiagrams\\ModelActivity1\\model.uml";
		String model2 = "D:\\documents\\A560169\\workspace\\Test_OCL2acsl\\TestDiagrams\\tests.uml";
		final EObject model = resourceSet
				.getResource(URI.createFileURI(model1), true).getContents()
				.get(0);
		UMLSwitch<EObject> umlSwitch = new UMLSwitch<EObject>() {

			@Override
			public EObject caseOperation(Operation op) {
				for (Constraint pre : op.getPreconditions()) {
					System.out.println(StaticOcl2Acsl.prepost2acsl(pre));
				}
				for (Constraint post : op.getPostconditions()) {
					System.out.println(StaticOcl2Acsl.prepost2acsl(post));
				}
				return super.caseOperation(op);
			}

		};

		for (Iterator<EObject> i = model.eAllContents(); i.hasNext();) {
			EObject object = i.next();
			umlSwitch.doSwitch(object);

		}
	}

	public static void main(String[] args) {
		testOcl2ACSL();
	}
}
