package keyext.extract_preconditions.ui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;

import javax.annotation.Nonnull;
import javax.swing.Action;
import java.util.List;

/**
 * GUI extension for precondition extractor functionality.
 */
@KeYGuiExtension.Info(name="Precondition extractor",
        description = "extract additional preconditions from open proofs",
        optional = true
)
public class PreconditionExtractorExt implements KeYGuiExtension, KeYGuiExtension.Startup, KeYGuiExtension.MainMenu {
    //TODO? expose the service calling functionality in the gui?

    private PreconditionExtractorAction preconditionExtractorAction;

    @Nonnull
    @Override
    public List<Action> getMainMenuActions(@Nonnull final MainWindow mainWindow) {
        init(mainWindow);
        return List.of(preconditionExtractorAction);
    }

    @Override
    public void init(final MainWindow window, final KeYMediator mediator) {
        init(window);

    }

    // why the heck gets init(MainWindow, KeYMediator) called after getMainMenuActions()?
    private void init(final MainWindow window) {
        if (preconditionExtractorAction != null) {
            // already inited
            return;
        }
        preconditionExtractorAction = new PreconditionExtractorAction(window);
        //TODO: deactivate action while not applicable (no proof selected, proof closed)

    }
}
