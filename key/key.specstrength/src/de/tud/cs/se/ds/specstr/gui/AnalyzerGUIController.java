// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.tud.cs.se.ds.specstr.gui;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import javax.swing.SwingUtilities;

import org.apache.logging.log4j.Level;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.core.Appender;
import org.apache.logging.log4j.core.Filter;
import org.apache.logging.log4j.core.LoggerContext;
import org.apache.logging.log4j.core.appender.OutputStreamAppender;
import org.apache.logging.log4j.core.config.Configuration;
import org.apache.logging.log4j.core.config.LoggerConfig;
import org.apache.logging.log4j.core.layout.PatternLayout;

import com.uwyn.jhighlight.renderer.XhtmlRendererFactory;

import de.tud.cs.se.ds.specstr.analyzer.Analyzer;
import de.tud.cs.se.ds.specstr.analyzer.Analyzer.AnalyzerResult;
import de.tud.cs.se.ds.specstr.analyzer.SymbExInterface;
import de.tud.cs.se.ds.specstr.util.JavaTypeInterface;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.application.Platform;
import javafx.beans.binding.Bindings;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.concurrent.Task;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.Cursor;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.Priority;
import javafx.scene.web.WebView;
import javafx.stage.FileChooser;
import javafx.stage.FileChooser.ExtensionFilter;
import javafx.stage.Window;

/**
 * TODO: Document.
 *
 * @author Dominic Steinhoefel
 */
public class AnalyzerGUIController {

    ////// FXML fields

    @FXML
    private TextField txtJavaFile;

    @FXML
    private Button btnFileChooser;

    @FXML
    private Button btnOpenKeY;

    @FXML
    private ComboBox<IObserverFunction> cmbMethodChooser;

    @FXML
    private Button btnStartAnalysis;

    @FXML
    private WebView wvInfo;

    ////// Private constants

    private static final File TMP_DIR = new File(
            System.getProperty("java.io.tmpdir") + "/analyzerOutput/");
    ////// Private properties

    private ObjectProperty<Window> mainWindowProperty =
            new SimpleObjectProperty<>();

    private ObjectProperty<File> javaFileProperty =
            new SimpleObjectProperty<>();

    private BooleanProperty interfaceDisabledProperty =
            new SimpleBooleanProperty(false);

    private ObjectProperty<File> proofFileProperty =
            new SimpleObjectProperty<>();

    ////// Initializer and public interface

    public void initialize() {
        if (!TMP_DIR.exists()) {
            if (!TMP_DIR.mkdirs()) {
                handleException(new RuntimeException(String.format(
                        "Could not create temporary directory %s",
                        TMP_DIR.getAbsolutePath())));
            }
        }

        txtJavaFile.textProperty().bind(Bindings.when(javaFileProperty.isNull())
                .then("")
                .otherwise(javaFileProperty.asString()));

        txtJavaFile.textProperty().addListener((obs, oldV, newV) -> {
            txtJavaFile.selectPositionCaret(newV.length() - 1);
        });

        mainWindowProperty.addListener(w -> {
            @SuppressWarnings("unchecked")
            final AnchorPane root =
                    (AnchorPane) ((ObjectProperty<Window>) w).get().getScene()
                            .getRoot();

            wvInfo.prefWidthProperty().bind(root.widthProperty().subtract(290));
            wvInfo.prefHeightProperty()
                    .bind(root.heightProperty().subtract(20));
        });

        javaFileProperty.addListener(l -> {
            try {
                @SuppressWarnings("unchecked")
                final ObjectProperty<File> objectProperty =
                        (ObjectProperty<File>) l;
                final String file = new String(Files.readAllBytes(
                        objectProperty.get().toPath()));
                loadTextToWebView(file, true);
            }
            catch (IOException e) {
                handleException(e);
            }
        });

    }

    public void setMainWindow(Window mainWindow) {
        mainWindowProperty.set(mainWindow);

        recursivelyDoForChildren(mainWindow.sceneProperty().get().getRoot(),
                n -> {
                    if (n instanceof Control
                            && !(n instanceof ScrollBar)) {
                        final Control ctrl = (Control) n;
                        ctrl.disableProperty()
                                .bind(interfaceDisabledProperty);
                    }
                });

        btnOpenKeY.disableProperty()
                .bind(proofFileProperty.isNull().or(interfaceDisabledProperty));

        cmbMethodChooser.disableProperty()
                .bind(javaFileProperty.isNull().or(interfaceDisabledProperty));

        btnStartAnalysis.disableProperty()
                .bind(cmbMethodChooser.selectionModelProperty().getValue()
                        .selectedItemProperty().isNull()
                        .or(interfaceDisabledProperty));
    }

    ////// FXML event handlers

    @FXML
    public void handleMethodSelected(ActionEvent e) {
        IObserverFunction selected =
                cmbMethodChooser.getSelectionModel().getSelectedItem();

        if (selected == null) {
            return;
        }

        StringWriter sw = new StringWriter();
        PrettyPrinter pw = new PrettyPrinter(sw, false, true);
        try {
            ((ProgramMethod) selected).prettyPrint(pw);
            loadTextToWebView(sw.getBuffer().toString(), true);
        }
        catch (IOException ex) {
            handleException(ex);
        }

        proofFileProperty.set(null);
    }

    @FXML
    public void handleAnalyzeButtonPressed() {
        final String methodDescriptor = JavaTypeInterface.getMethodDescriptor(
                (IProgramMethod) cmbMethodChooser.getSelectionModel()
                        .getSelectedItem());
        final File outProofFile = new File(TMP_DIR,
                methodDescriptor + ".proof");
        final Analyzer analyzer = new Analyzer(javaFileProperty.get(),
                methodDescriptor,
                Optional.of(outProofFile));

        proofFileProperty.set(outProofFile);

        Task<AnalyzerResult> task = new Task<AnalyzerResult>() {
            @Override
            protected AnalyzerResult call() throws Exception {
                return doWithDisabledWindow(() -> {
                    AnalyzerResult result = null;
                    Logger logger =
                            LogManager.getLogger(AnalyzerGUIController.class);
                    try (WebViewOutputStream webViewOutputStream =
                            new WebViewOutputStream()) {
                        appendWebViewLogger(webViewOutputStream);
                        result = analyzer.analyze();
                    }

                    // Funny hack for "null-terminating" the log stream --
                    // without that, somehow the log buffer is not reset.
                    logger.info("\0");

                    return result;
                });
            }
        };

        Thread th = new Thread(task);
        th.setDaemon(true);
        th.start();

        task.setOnSucceeded(ev -> {
            AnalyzerResult result;
            try {
                result = task.get();

                ByteArrayOutputStream os = new ByteArrayOutputStream();
                Analyzer.printResults(result, new PrintStream(os));
                String resultStr = new String(os.toByteArray(), "UTF-8");

                loadTextToWebView(resultStr, false);
            }
            catch (InterruptedException | ExecutionException
                    | IOException ex) {
                handleException(ex);
            }
        });
    }

    @FXML
    public void handleOpenKeYButtonPressed() {
        SwingUtilities.invokeLater(() -> {
            MainWindow keyWin = MainWindow.getInstance(true);
            keyWin.loadProblem(proofFileProperty.get());
        });
    }

    @FXML
    public void handleChooseFilePressed() {
        final FileChooser fileChooser = new FileChooser();
        fileChooser.setTitle("Open Resource File");
        fileChooser.getExtensionFilters().addAll(
                new ExtensionFilter("Java Files", "*.java"));

        final File selectedFile =
                fileChooser.showOpenDialog(mainWindowProperty.get());
        if (selectedFile != null) {
            javaFileProperty.set(selectedFile);

            Task<Void> task = new Task<Void>() {
                @Override
                protected Void call() throws Exception {
                    return doWithDisabledWindow(() -> {
                        loadContractTargets(selectedFile);
                        return null;
                    });
                }
            };

            Thread th = new Thread(task);
            th.setDaemon(true);
            th.start();
        }

        proofFileProperty.set(null);
    }

    /////// Private helpers

    private void recursivelyDoForChildren(Parent node, Consumer<Node> job) {
        for (final Node child : node
                .getChildrenUnmodifiable()) {
            job.accept(child);
            if (child instanceof Parent
                    && !((Parent) child).getChildrenUnmodifiable().isEmpty()) {
                recursivelyDoForChildren((Parent) child, job);
            }
        }
    }

    private void loadContractTargets(final File selectedFile) {
        try {
            final SymbExInterface seIf =
                    new SymbExInterface(selectedFile);
            final List<KeYJavaType> types = seIf.getDeclaredTypes();
            final List<IObserverFunction> contractTargets = types
                    .stream()
                    .filter(t -> t
                            .getJavaType() instanceof TypeDeclaration
                            && !((TypeDeclaration) t.getJavaType())
                                    .isLibraryClass())
                    .map(t -> seIf.keyEnvironment()
                            .getSpecificationRepository()
                            .getContractTargets(t).stream()
                            .collect(Collectors.toList()))
                    .flatMap(List::stream)
                    .collect(Collectors.toList());
            Platform.runLater(() -> {
                cmbMethodChooser.setItems(FXCollections
                        .observableArrayList(contractTargets));
            });
        }
        catch (ProblemLoaderException e) {
            handleException(e);
        }
    }

    private <A> A doWithDisabledWindow(Callable<A> lambda) {
        final Scene scene = mainWindowProperty.get().getScene();

        interfaceDisabledProperty.set(true);
        scene.setCursor(Cursor.WAIT);

        A result = null;
        try {
            result = lambda.call();
        }
        catch (Exception e) {
            handleException(e);
        }

        interfaceDisabledProperty.set(false);
        scene.setCursor(Cursor.DEFAULT);

        return result;
    }

    private void appendWebViewLogger(
            final WebViewOutputStream webViewOutputStream) {
        final Configuration config =
                LoggerContext.getContext(false).getConfiguration();
        final PatternLayout layout =
                PatternLayout.createDefaultLayout(config);
        final Appender appender =
                OutputStreamAppender.createAppender(layout, null,
                        webViewOutputStream, "WebViewAppender",
                        false, true);
        appender.start();
        config.addAppender(appender);

        final Level level = null;
        final Filter filter = null;
        for (final LoggerConfig loggerConfig : config.getLoggers()
                .values()) {
            loggerConfig.addAppender(appender, level, filter);
        }
        config.getRootLogger().addAppender(appender, level, filter);
    }

    private void loadTextToWebView(String text, boolean javaHighlight) {
        wvInfo.getEngine()
                .loadContent(new StringBuilder().append("<html>")
                        .append("<head>")
                        .append("<style type=\"text/css\">")
                        .append(XhtmlRendererFactory.getRenderer("java").getCssClassDefinitions())
                        .append("</style>")
                        .append("</head>")
                        .append("<body>")
                        .append(text2HTML(text, javaHighlight))
                        .append("</body>")
                        .append("</html>").toString());
    }

    private String text2HTML(String text, boolean javaHighlight) {
        if (javaHighlight) {
            InputStream in = new ByteArrayInputStream(
                    text.getBytes(StandardCharsets.UTF_8));
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            try {
                XhtmlRendererFactory.getRenderer("java") //
                        .highlight("", //
                                in, //
                                out, //
                                "utf-8", //
                                true);
                text = out.toString("utf-8");
                in.close();
                out.close();
            }
            catch (IOException e) {
                handleException(e);
            }
        }
        else {
            text = text.replaceAll("\n", "<br/>")
                    .replaceAll(" ", "&nbsp;");
        }

        return text;
    }

    private void handleException(Exception e) {
        Alert alert = new Alert(AlertType.ERROR);
        alert.setTitle("Exception Dialog");
        alert.setHeaderText("Sorry, an exception occurred.");
        alert.setContentText(e.getMessage());

        // Create expandable Exception.
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        e.printStackTrace(pw);
        String exceptionText = sw.toString();

        Label label = new Label("The exception stacktrace was:");

        TextArea textArea = new TextArea(exceptionText);
        textArea.setEditable(false);
        textArea.setWrapText(true);

        textArea.setMaxWidth(Double.MAX_VALUE);
        textArea.setMaxHeight(Double.MAX_VALUE);
        GridPane.setVgrow(textArea, Priority.ALWAYS);
        GridPane.setHgrow(textArea, Priority.ALWAYS);

        GridPane expContent = new GridPane();
        expContent.setMaxWidth(Double.MAX_VALUE);
        expContent.add(label, 0, 0);
        expContent.add(textArea, 0, 1);

        // Set expandable Exception into the dialog pane.
        alert.getDialogPane().setExpandableContent(expContent);

        alert.showAndWait();
    }

    ////// Inner classes

    private class WebViewOutputStream extends OutputStream {
        private String str = "";

        @Override
        public void write(int b) throws IOException {
            if (b == 0) {
                str = "";
                return;
            }

            str += (char) b;
            Platform.runLater(() -> {
                loadTextToWebView(str.trim(), false);
            });
        }

        @Override
        public void close() throws IOException {
            str = "";
        }

    }
}
