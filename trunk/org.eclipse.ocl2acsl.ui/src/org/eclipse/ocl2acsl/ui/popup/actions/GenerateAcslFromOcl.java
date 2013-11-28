package org.eclipse.ocl2acsl.ui.popup.actions;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.emf.common.util.BasicMonitor;
import org.eclipse.emf.common.util.URI;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ocl2acsl.acceleo.common.Generate;
import org.eclipse.ocl2acsl.ui.Activator;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;


public class GenerateAcslFromOcl implements IObjectActionDelegate {

	private ISelection selection;
	
	/**
	 * Constructor for Action1.
	 */
	public GenerateAcslFromOcl() {
		super();
	}

	/**
	 * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
	 */
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}

	/**
	 * @see IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		IRunnableWithProgress operation = new IRunnableWithProgress() {
			public void run(IProgressMonitor monitor) {
				IFile model = null;
				try {
					model = getFile();
					URI modelURI = URI.createPlatformResourceURI(model.getFullPath().toString(), true);
					File target = new File(ResourcesPlugin.getWorkspace().getRoot().getLocationURI().getPath() +  model.getFullPath().removeLastSegments(1) + "/gen-fc/");
					Generate generator = new Generate(modelURI,target,getArguments());
					generator.doGenerate(new BasicMonitor());
				} catch (Exception e) {
					IStatus status = new Status(IStatus.ERROR,
							Activator.PLUGIN_ID, e.getMessage(), e);
					Activator.getLogger().log(status);
				} finally {
					try {
						model.getProject().refreshLocal(
								IResource.DEPTH_INFINITE, monitor);
						monitor.done();
					} catch (CoreException e) {
						IStatus status = new Status(IStatus.ERROR,
								Activator.PLUGIN_ID, e.getMessage(), e);
						Activator.getLogger().log(status);
					}
				}
			}
		};
		try {
			PlatformUI.getWorkbench().getProgressService()
					.run(true, true, operation);
		} catch (Exception e) {
			IStatus status = new Status(IStatus.ERROR, Activator.PLUGIN_ID,
					e.getMessage(), e);
			Activator.getLogger().log(status);
		}
	}

	/**
	 * @see IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection;
	}
	
	private IFile getFile() {
		return (IFile) ((IStructuredSelection) selection).getFirstElement();
	}
	
	protected List<? extends Object> getArguments() {
		return new ArrayList<String>();
	}

}
