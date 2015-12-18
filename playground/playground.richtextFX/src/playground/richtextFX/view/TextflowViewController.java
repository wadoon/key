package playground.richtextFX.view;

import java.io.File;
import java.net.URL;
import java.util.ResourceBundle;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javafx.fxml.FXML;
import javafx.scene.control.CheckBox;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.layout.Pane;
import javafx.scene.paint.Color;
import javafx.scene.text.TextFlow;
import javafx.scene.web.WebEngine;
import playground.richtextFX.KeYView;
import playground.richtextFX.ViewController;
import playground.richtextFX.ViewPosition;
import playground.richtextFX.util.CustomText;

@KeYView(title = "Textflow", path = "TextflowView.fxml", preferredPosition = ViewPosition.CENTER)

public class TextflowViewController extends ViewController {

    private boolean sequentLoaded = false;
    //private SequentPrinter printer;
    private LogicPrinter logicPrinter;
    private String proofString;
    private WebEngine webEngine;
    private NotationInfo notationInfo = new NotationInfo();
    private Services services;
    private Sequent sequent;

    // @FXML
    // private TextArea textArea;

    @FXML
    private CheckBox checkBoxPrettySyntax;

    @FXML
    private CheckBox checkBoxUnicode;

    @FXML
    private TextFlow textFlow;

    @FXML
    private ToggleButton filterButton;

    @FXML
    private Pane filterParent;

    @FXML
    private TextField filterText;

    @FXML
    private TextField searchBox;
    /*
    private EventHandler<MouseEvent> mousehandler = new EventHandler<MouseEvent>() {

        @Override
        public void handle(MouseEvent mouseEvent) {

            System.out.println(
                    mouseEvent.getEventType() + "\n" + "X : Y - " + mouseEvent.getX() + " : " + mouseEvent.getY() + "\n"
                            + "SceneX : SceneY - " + mouseEvent.getSceneX() + " : " + mouseEvent.getSceneY() + "\n"
                            + "ScreenX : ScreenY - " + mouseEvent.getScreenX() + " : " + mouseEvent.getScreenY());

        }
    };*/
    
    
    
    
    /**
     * The constructor. The constructor is called before the initialize()
     * method.
     */
    public TextflowViewController() {
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        // hide the filter at the beginning
        toggleFilter();
        //initializeSearchBox();
        System.out.println("init");
        /*
        textAreaCodeArea.setMouseOverTextDelay(Duration.ofSeconds(1));
        textAreaCodeArea.addEventHandler(MouseOverTextEvent.MOUSE_OVER_TEXT_BEGIN, e -> {
            int chIdx = e.getCharacterIndex();
            System.out.println(chIdx);
            javafx.geometry.Point2D pos = e.getScreenPosition();
            mainApp.setPopUp("Character '" + textAreaCodeArea.getText(chIdx, chIdx+1) + "' at " + pos);
            mainApp.showPopUp(textAreaCodeArea, pos.getX(), pos.getY() + 10);
        });
        textAreaCodeArea.addEventHandler(MouseOverTextEvent.MOUSE_OVER_TEXT_END, e -> {
            mainApp.hidePopUp();
        });*/
        
    }
    /*
    private void initializeSearchBox() {
        searchBox.setText("Search...");
        searchBox.focusedProperty().addListener(new ChangeListener<Boolean>() {
            @Override
            public void changed(ObservableValue<? extends Boolean> arg0, Boolean oldPropertyValue,
                    Boolean newPropertyValue) {
                if (newPropertyValue) {
                    if (searchBox.getText().equals("Search..."))
                        searchBox.setText("");
                }
                else {
                    if (searchBox.getText().isEmpty())
                        searchBox.setText("Search...");
                }
            }
        });
        searchBox.setOnKeyReleased(new EventHandler<KeyEvent>() {
            public void handle(KeyEvent event) {
                printer.setFreeTextSearch(searchBox.getText());
                // highlight(searchBox.getText());
                // updateHtml(printer.printSequent(printer.highlightString(proofString,
                // searchBox.getText())));
                updateHtml(printer.printSequent(proofString));
                event.consume();
            }
        });
    }*/

    /**
     * After a proof has been loaded, the sequent of the root node will be
     * displayed
     */
    @FXML
    private void showRootSequent() {
        Proof proof = mainApp.getProof();
        if (proof == null) {
            mainApp.setStatus("Please Select a Proof first.");
            return;
        }
        services = proof.getServices();
        Node node = proof.root();
        sequent = node.sequent();

        logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
        notationInfo.refresh(services, false, false);
        printSequent();

        // textAreaWebView.setOnMouseMoved(mousehandler);
    }

    /**
     * Enables/Disables Pretty Syntax. Only works when a sequent is displayed.
     */
    @FXML
    private void usePrettySyntax() {
        if (!sequentLoaded) {
            mainApp.setStatus("Please load and diplay a proof first.");
            checkBoxPrettySyntax.setSelected(false);
            return;
        }
        else if (notationInfo.isPrettySyntax()) {
            logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
            notationInfo.refresh(services, false, false);
            checkBoxPrettySyntax.setSelected(false);
            checkBoxUnicode.setSelected(false);
            printSequent();
            return;
        }
        else {
            logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
            notationInfo.refresh(services, true, false);
            checkBoxPrettySyntax.setSelected(true);
            printSequent();
        }
    }

    /**
     * Enables/Disables Unicode. Only works when a sequent is displayed and
     * Pretty Syntax is enabled.
     */
    @FXML
    private void useUnicode() {
        if (!notationInfo.isPrettySyntax() || !sequentLoaded) {
            mainApp.setStatus("Please enable Pretty Syntax first.");
            checkBoxUnicode.setSelected(false);
            return;
        }
        else if (notationInfo.isUnicodeEnabled()) {
            logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
            notationInfo.refresh(services, true, false);
            checkBoxUnicode.setSelected(false);
            printSequent();
            return;
        }
        else {
            logicPrinter = new LogicPrinter(new ProgramPrinter(), notationInfo, services);
            notationInfo.refresh(services, true, true);
            checkBoxUnicode.setSelected(true);
            printSequent();
        }
    }

    /**
     * Helper method to print a sequent into the webview.
     */
    private void printSequent() {
        logicPrinter.printSequent(sequent);
        proofString = logicPrinter.toString();

        //printer = new SequentPrinter("resources/css/sequentStyle.css", "resources/css/sequentClasses.ini");
        sequentLoaded = true;
        // System.out.println(printer.escape(proofString));
        //updateHtml(printer.printSequent(proofString));
        updateHtml(proofString);
    }

    /**
     * Loads a default proof and displays the sequent of its root node.
     */
    @FXML
    private void loadDefaultProof() {
        File file = new File("resources/proofs/gcd.closed.proof");
        mainApp.setProof(file);
        showRootSequent();
    }

    // TODO replace
    private void highlight(String s) {
        if (!s.isEmpty()) {
            String text = proofString;
            int lastIndex = 0;
            while (lastIndex != -1) {
                lastIndex = text.indexOf(s, lastIndex);

                if (lastIndex != -1) {
                    // TODO instead of printing the index, it should be
                    // highlighted in the textArea
                    System.out.println(lastIndex);
                    lastIndex += s.length();
                }
            }
        }
    }

    @FXML
    private void toggleFilter() {
        filterParent.managedProperty().bind(filterParent.visibleProperty());
        filterParent.setVisible(filterButton.isSelected());
    }

    private void updateHtml(String s) {
        //webEngine = textAreaWebView.getEngine();
        //webEngine.loadContent(s);
        //textAreaCodeArea.replaceText(s);
        // textAreaWebView.getEngine().loadContent(s);
        char[] ca= s.toCharArray(); 
        CustomText insertText;
        for (int i = 0; i < ca.length; i++){
            insertText = new CustomText(String.valueOf(ca[i]), i);
            if (i %20 == 0){
                insertText.setFill(Color.RED);
            }
            insertText.setOnMouseEntered(event ->{
                Object source = event.getSource();
                if (source instanceof CustomText) {
                    CustomText sourceText = (CustomText) source;
                    System.out.println(sourceText.getText());
                }
            });
            textFlow.getChildren().add(insertText);
           
        }
    }

    @FXML
    private void handleApplyFilter() {
        doFilter(filterText.getText());
    }

    // just dummy method
    private void doFilter(String filterstring) {
        if (!sequentLoaded)
            return;
        //printer.addTempCss("filterCss", String.format(".content %s * {display: none !important;}", filterstring));
        //updateHtml(printer.printSequent(proofString));
    }
}
