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

package org.eclipse.ocl2acsl.additionalOperations;

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
