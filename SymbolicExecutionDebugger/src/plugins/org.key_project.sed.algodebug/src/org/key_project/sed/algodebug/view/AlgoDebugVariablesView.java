/*******************************************************************************
 *  Copyright (c) 2000, 2013 IBM Corporation and others.
 *  All rights reserved. This program and the accompanying materials
 *  are made available under the terms of the Eclipse Public License v1.0
 *  which accompanies this distribution, and is available at
 *  http://www.eclipse.org/legal/epl-v10.html
 * 
 *  Contributors:
 *     IBM Corporation - initial API and implementation
 *     QNX Software Systems - Mikhail Khodjaiants - Registers View (Bug 53640)
 *     Wind River - Pawel Piech - Drag/Drop to Expressions View (Bug 184057)
 *       Wind River - Pawel Piech - Busy status while updates in progress (Bug 206822)
 *       Wind River - Pawel Piech - NPE when closing the Variables view (Bug 213719)
 *     Wind River - Pawel Piech - Fix viewer input race condition (Bug 234908)
 *     Wind River - Anton Leherbauer - Fix selection provider (Bug 254442)
 *     Patrick Chuong (Texas Instruments) - Improve usability of the breakpoint view (Bug 238956)
 *     Patrick Chuong (Texas Instruments) and Pawel Piech (Wind River) - 
 *          Allow multiple debug views and multiple debug context providers (Bug 327263)
 *******************************************************************************/
package org.key_project.sed.algodebug.view;

import org.eclipse.debug.internal.ui.views.variables.VariablesView;

/**
 * This view shows variables and their values for a particular stack frame
 */
@SuppressWarnings("restriction")
public class AlgoDebugVariablesView extends VariablesView {
   
}
