package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.SpecNameLabel;
import de.uka.ilkd.key.pp.AbbrevException;

import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.util.Iterator;
import java.util.Objects;

/**
 * @author Alexander Weigl
 * @version 1 (1/16/22)
 */
public class MakeNamedFormulaToAbbrevAction extends MainWindowAction {
    public MakeNamedFormulaToAbbrevAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Introduce abbreviation for named formulas");

        setEnabled(mainWindow.getMediator().getSelectedNode() != null);
        mainWindow.getMediator().addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                setEnabled(mainWindow.getMediator().getSelectedNode() != null);
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
            }
        });
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        var node = Objects.requireNonNull(mainWindow.getMediator().getSelectedNode());
        findAndIntroduce(node.sequent().antecedent().iterator());
        findAndIntroduce(node.sequent().succedent().iterator());

        if ((e.getModifiers() & InputEvent.SHIFT_DOWN_MASK) != 0) {
            mainWindow.getVisibleTermLabels().setHidden(SpecNameLabel.NAME, true);
        }
    }

    private void findAndIntroduce(Iterator<SequentFormula> iterator) {
        iterator.forEachRemaining(it -> findAndIntroduce(it.formula()));
    }

    private void findAndIntroduce(Term t) {
        var l = (SpecNameLabel) t.getLabel(SpecNameLabel.NAME);
        if (l != null) {
            try {
                getMediator().getNotationInfo().getAbbrevMap().put(t, l.getName(), true);
            } catch (AbbrevException e) {
                e.printStackTrace();
            }
        }

        for (Term sub : t.subs()) {
            findAndIntroduce(sub);
        }
    }
}