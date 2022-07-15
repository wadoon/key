package keyext.extract_preconditions.ui;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import keyext.extract_preconditions.PreconditionExtractor;
import keyext.extract_preconditions.projections.AbstractTermProjection;
import keyext.extract_preconditions.projections.SimpleProjection;

import javax.annotation.Nonnull;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.SwingWorker;
import javax.swing.WindowConstants;
import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.util.concurrent.ExecutionException;

public class PreconditionExtractorDialog extends JDialog {

    private final JTextArea textArea;
    private final JButton startButton;
    public PreconditionExtractorDialog(final @Nonnull MainWindow mainWindow) {
        super(mainWindow);

        setModal(false);
        setSize(1000, 700);
        setTitle("Precondition Extraction");
        setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        setLayout(new BorderLayout());

        textArea = new JTextArea();
        final JScrollPane scrollpane = new JScrollPane(textArea);
        final JPanel flowPanel = new JPanel(new FlowLayout());

        scrollpane.setHorizontalScrollBarPolicy(
                ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        scrollpane.setVerticalScrollBarPolicy(
                ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS);
        startButton = new JButton(new KeyAction() {
            @Override
            public void actionPerformed(final ActionEvent e) {
                final Proof proof = mainWindow.getMediator().getSelectedProof();
                if (proof == null || proof.closed()) {
                    //TODO: deactivate startbutton while no proof is selected.
                    return;
                }
                //TODO: make projection configurable.
                final Worker worker = new Worker(proof,
                        textArea,  new SimpleProjection(proof.getServices()), mainWindow.getUserInterface());
                worker.execute();
                //TODO: allow to cancel worker.
            }
        });
        startButton.setText("Extract Preconditions");
        flowPanel.add(startButton);
        add(scrollpane, BorderLayout.CENTER);
        add(flowPanel, BorderLayout.SOUTH);
    }

    private static class Worker extends SwingWorker<Term, Void> {

        private final Proof proof;
        private final JTextArea textArea;
        private final UserInterfaceControl uiControl;
        private final AbstractTermProjection projection;


        private Worker(final @Nonnull Proof proof, final @Nonnull JTextArea textArea,
                       final @Nonnull AbstractTermProjection projection,
                       final @Nonnull UserInterfaceControl uiControl) {
            this.proof = proof;
            this.textArea = textArea;
            this.uiControl = uiControl;
            this.projection = projection;
        }

        @Override
        protected Term doInBackground() throws Exception {
            final Services services = proof.getServices();
            final PreconditionExtractor extractor = new PreconditionExtractor(proof, uiControl, projection);
            //TODO: figure out how to correctly connect those Terms.
            // a comment in that extractor code says all of these should get ORed,
            // but the result doesn't seem like a valid precondition for my example
            // just @ensures 0 <= f <= 127 { return f; } produces f >= 128 || f <= -1, maybe a NOR?
            //TODO: simplify connected precondition (it has redundant subterms).
            //TODO: translate to jml.
            return services.getTermBuilder().or(extractor.extract().first);
        }

        @Override
        protected void done() {
            if (isCancelled()) {
                // cancelled instead, no result
                return;
            }
            try {
                textArea.setText(LogicPrinter.quickPrintTerm(get(), proof.getServices()));
            } catch (InterruptedException e) {
                // shouldn't happen: computation is done
                throw new RuntimeException(e);
            } catch (ExecutionException e) {
                // there seems to be no way to ask before if there was some exception thrown
                throw new RuntimeException(e);
            }
        }
    }
}
