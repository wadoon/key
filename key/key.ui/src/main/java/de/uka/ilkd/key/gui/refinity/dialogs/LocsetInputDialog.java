// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.refinity.dialogs;

import java.awt.Window;
import java.util.Optional;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.refinity.model.FuncOrPredDecl;
import de.uka.ilkd.key.abstractexecution.refinity.model.FunctionDeclaration;
import de.uka.ilkd.key.java.Services;

/**
 * @author Dominic Steinhoefel
 */
public class LocsetInputDialog extends FuncAndPredInputDialog {
    private static final long serialVersionUID = 1L;

    public LocsetInputDialog(final Window owner, final FunctionDeclaration value,
            Services services) {
        super(owner, value, services);
    }

    @Override
    protected FunctionDeclaration parseString(String input) throws IllegalArgumentException {
        final Optional<FunctionDeclaration> result = //
                FunctionDeclaration.fromString("LocSet " + input);

        if (!result.isPresent()) {
            throw new IllegalArgumentException();
        }

        return result.get();
    }

    @Override
    protected String renderValue(FuncOrPredDecl value) {
        if (value.getArgSorts().isEmpty()) {
            return value.getName();
        }

        return String.format("%s(%s)", value.getName(),
                value.getArgSorts().stream().collect(Collectors.joining(", ")));
    }

    @Override
    protected String inputTooltipText() {
        return "<html>Example: \"<tt>MyAbstrLocSet</tt>\", \"<tt>SubFrame(int)</tt>\"</html>";
    }

    @Override
    protected String windowTitle() {
        return "Please enter a nullary or parametrized abstract location set specification.";
    }

    public static FunctionDeclaration showInputDialog(final Window owner, Services services) {
        return showInputDialog(owner, new FunctionDeclaration("", ""), services);
    }

    public static FunctionDeclaration showInputDialog(final Window owner,
            final FunctionDeclaration value, Services services) {
        final LocsetInputDialog dia = new LocsetInputDialog(owner, value, services);
        dia.setVisible(true);
        dia.dispose();
        return (FunctionDeclaration) dia.getValue();
    }

}
