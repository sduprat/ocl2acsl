package org.eclipse.ocl2acsl;

/**
 * Exception thrown by the OCL parser if it fails to parse the OCL expression
 * 
 * @author A560169
 * 
 */
public class OCL2acslParserException extends Exception {

	private static final long serialVersionUID = 1L;
	private final Exception e;

	public OCL2acslParserException(Exception e) {
		this.e = e;
	}

	@Override
	public String getMessage() {
		return e.getMessage();
	}

	@Override
	public String getLocalizedMessage() {
		return e.getLocalizedMessage();
	}

}
