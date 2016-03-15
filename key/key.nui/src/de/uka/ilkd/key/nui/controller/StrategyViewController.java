package de.uka.ilkd.key.nui.controller;

import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.exceptions.ControllerNotFoundException;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.ProofStarter;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.Slider;
import javafx.scene.control.ToggleGroup;
import javafx.scene.image.ImageView;
import javafx.util.StringConverter;

/**
 * Controller for StrategyView GUI element, used to show proof strategy options.
 * 
 * @author Florian Breitfelder
 *
 */
@ControllerAnnotation(createMenu = true)
public class StrategyViewController extends NUIController {

    @FXML
    private Button goButton;

    @FXML
    private Slider maxRuleAppSlider;

    @FXML
    private Label maxRuleAppLabel;

    @FXML
    private ImageView goButtonImage;

    @FXML
    private ToggleGroup stopAt;

    @FXML
    private ToggleGroup proofSplitting;

    @FXML
    private ToggleGroup loopTreatment;

    @FXML
    private ToggleGroup blockTreatment;

    @FXML
    private ToggleGroup methodTreatment;

    @FXML
    private ToggleGroup dependencyContracts;

    @FXML
    private ToggleGroup queryTreatment;

    @FXML
    private ToggleGroup expandLocalQueries;

    @FXML
    private ToggleGroup arithmeticTreatment;

    @FXML
    private ToggleGroup quantifierTreatment;

    @FXML
    private ToggleGroup classAxiom;

    @FXML
    private ToggleGroup autoInduction;

    @FXML
    private ToggleGroup userOptions1;

    @FXML
    private ToggleGroup userOptions2;

    @FXML
    private ToggleGroup userOptions3;

    private int currentSliderValue = 10;

    @Override
    protected void init() {
        // Set image of the 'GO' button
        IconFactory iconFactory = new IconFactory(15, 15);
        goButtonImage.setImage(
                iconFactory.getImage(IconFactory.GO_BUTTON).getImage());

        // Set formatter of 'Maximum rules' slider
        maxRuleAppSlider.setLabelFormatter(new StringConverter<Double>() {
            @Override
            public String toString(Double n) {
                int val = (int) Math.pow(10, n);
                return "" + (val >= 10000 ? val >= 1000000
                        ? (val / 1000000) + "M" : (val / 1000) + "k" : +val);
            }

            @Override
            public Double fromString(String string) {
                return null;
            }
        });

        // Adds a listener to the 'Maximum rules' slider, used to update the
        // label with the currently chosen value
        maxRuleAppSlider.valueProperty().addListener((ov, old_val, new_val) -> {
            calculateCurrentSliderValue(new_val);
            maxRuleAppLabel.setText(bundle.getString("maxRuleAppLabel") + " "
                    + currentSliderValue);
        });
        maxRuleAppLabel.setText(
                bundle.getString("maxRuleAppLabel") + " " + currentSliderValue);
    }

    public void handleOnAction(final ActionEvent e)
            throws ControllerNotFoundException {

        ProofStarter proofStarter = new ProofStarter(false);
        String filename;

        try {
            filename = dataModel.getLoadedTreeViewState().getProof()
                    .getProofFile().getName();
        }
        catch (NullPointerException e2) {
            nui.updateStatusbar(bundle.getString("errorProofFileMissing"));
            return;
        }

        // retrieve proof file and init proofStarter
        TreeViewState treeViewState = dataModel.getTreeViewState(filename);
        Proof p = treeViewState.getProof();
        proofStarter.init(p);

        // restrict maximum number of rule applications based on slider value
        // only set value of slider if slider was moved
        if (currentSliderValue > 0) {
            proofStarter.setMaxRuleApplications(currentSliderValue);
        }

        // start automatic proof
        ApplyStrategyInfo strategyInfo = proofStarter.start();

        // update statusbar
        nui.updateStatusbar(strategyInfo.reason());

        // if automatic rule application could not be performed -> no rendering
        // of proof required
        if (strategyInfo.getAppliedRuleApps() > 0) {
            // load updated proof
            Proof updatedProof = proofStarter.getProof();

            // create new tree from updateProof
            ProofTreeItem fxtree = new ProofTreeConverter(updatedProof)
                    .createFXProofTree();

            // Create new TreeViewState for updatedProof
            TreeViewState updatedTreeViewState = new TreeViewState(updatedProof,
                    fxtree);

            // update datamodel
            dataModel.saveTreeViewState(updatedTreeViewState, filename);

        }
    }

    /**
     * Calculates the value of the slider based on the current position.
     * 
     * @param new_val
     *            {@link Number} the value obtained from the slider.
     */
    private void calculateCurrentSliderValue(Number new_val) {
        double sliderValue = new_val.doubleValue();

        if (sliderValue > 0.0 && sliderValue < 1.0) {
            currentSliderValue = ((int) (sliderValue % 9.0 * 10.0)) + 1;
        }
        else if (sliderValue > 1.0 && sliderValue < 2.0) {
            currentSliderValue = ((int) (((sliderValue % 9.0) - 1) * 10) * 10)
                    + 10;
        }
        else if (sliderValue > 2.0 && sliderValue < 3.0) {
            currentSliderValue = ((int) (((sliderValue % 9.0) - 2) * 10) * 100)
                    + 100;
        }
        else if (sliderValue > 3.0 && sliderValue < 4.0) {
            currentSliderValue = ((int) (((sliderValue % 9.0) - 3) * 10) * 1000)
                    + 1000;
        }
        else if (sliderValue > 4.0 && sliderValue < 5.0) {
            currentSliderValue = ((int) (((sliderValue % 9.0) - 4) * 10)
                    * 10000) + 10000;
        }
        else if (sliderValue > 5.0 && sliderValue < 6.0) {
            currentSliderValue = ((int) (((sliderValue % 9.0) - 5) * 10)
                    * 100000) + 100000;
        }
        else {
            switch (new_val.intValue()) {
            case 1:
                currentSliderValue = 10;
                break;
            case 2:
                currentSliderValue = 100;
                break;
            case 3:
                currentSliderValue = 1000;
                break;
            case 4:
                currentSliderValue = 10000;
                break;
            case 5:
                currentSliderValue = 100000;
                break;
            case 6:
                currentSliderValue = 1000000;
                break;
            }
        }
    }
}
