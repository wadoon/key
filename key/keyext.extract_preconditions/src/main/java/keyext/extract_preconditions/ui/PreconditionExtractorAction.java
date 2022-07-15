package keyext.extract_preconditions.ui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import javax.swing.Icon;
import java.awt.event.ActionEvent;

public class PreconditionExtractorAction extends MainWindowAction {

    private static final String NAME = "Extract preconditions";
    private static final String TOOLTIP = "Extract preconditions from open goals";

    protected PreconditionExtractorAction(final MainWindow mainWindow) {
        super(mainWindow);
        setName(NAME);
        setTooltip(TOOLTIP);
        Icon icon = IconFactory.testGeneration(MainWindow.TOOLBAR_ICON_SIZE);
        putValue(SMALL_ICON, icon);
        setMenuPath("Proof");
    }

    @Override
    public void actionPerformed(final ActionEvent e) {
        final PreconditionExtractorDialog dialog = new PreconditionExtractorDialog(mainWindow);
        dialog.setVisible(true);
    }
}
