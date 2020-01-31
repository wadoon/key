// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.abstractexecution.rule.metaconstruct;

import de.uka.ilkd.key.logic.Name;

/**
 * Term transformer for linking a completion type specifier in the context of
 * abstract execution to its precondition. More precisely, it creates the
 * formula "(specifier <-> PRECONDITION)", where "specifier" might be a term
 * like "returns_P(accessibles)".
 * 
 * <p>
 * Syntax:
 * <code>#postCondAE(#absProg, "&lt;COMPLETION_TYPE&gt;", #returns, #result, #exc, #breaks, #returns)</code>
 *
 * @author Dominic Steinhoefel
 */
public class RetrieveAEPostconditionTransformerLoop extends AbstractRetrieveAEPostconditionTransformer {
    public RetrieveAEPostconditionTransformerLoop() {
        super(new Name("#postCondAELoop"), 7);
    }

}