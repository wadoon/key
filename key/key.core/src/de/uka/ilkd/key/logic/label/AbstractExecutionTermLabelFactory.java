// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.TermServices;

/**
 * A {@link TermLabelFactory} for {@link AbstractExecutionTermLabel}s. This
 * factory cannot actually create objects from {@link String}s, so it might be
 * considered a little useless; however, it is needed for turning off and on the
 * display of {@link AbstractExecutionTermLabel}s in the GUI.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExecutionTermLabelFactory
        implements TermLabelFactory<AbstractExecutionTermLabel> {

    @Override
    public AbstractExecutionTermLabel parseInstance(List<String> arguments,
            TermServices services) throws TermLabelException {
        return null;
    }

}
