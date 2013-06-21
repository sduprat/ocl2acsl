package org.eclipse.ocl2acsl;

public class OCL2acslParserException extends Exception {
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
