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
