package edu.kit.iti.formal.psdbg.interpreter.funchdl;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.SavePoint;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import edu.kit.iti.formal.psdbg.storage.KeyPersistentFacade;
import javafx.application.Platform;
import javafx.scene.control.Alert;
import javafx.scene.control.ButtonType;
import lombok.Getter;
import lombok.Setter;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import javax.annotation.Nullable;
import javax.xml.bind.JAXBException;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.util.Optional;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.locks.ReentrantLock;

public class SaveCommand implements CommandHandler<KeyData> {
    public static final String SAVE_COMMAND_NAME = "#save";
    private static Logger logger = LogManager.getLogger(SaveCommand.class);
    private static Logger consoleLogger = LogManager.getLogger("console");

    @Getter
    @Setter
    private File path;

    public SaveCommand(File path) {
        this.path = path;
    }


    @Override
    public boolean handles(CallStatement call, @Nullable KeyData data) throws IllegalArgumentException {
        return call.getCommand().equals(SAVE_COMMAND_NAME);
    }

    @Override
    public void evaluate(Interpreter<KeyData> interpreter, CallStatement call, VariableAssignment params, KeyData data) {
        //be careful parameters are uninterpreted
        SavePoint sp = new SavePoint(call);
        //Not via Parentpath -> dependency on OS
           /*     String parentPath = path.getAbsolutePath();
        parentPath = parentPath.substring(0, parentPath.length() - path.getName().length());*/

        File parent = path.getParentFile();
        File newFile = sp.getProofFile(parent);

        consoleLogger.info("(Safepoint) Location to be saved to = " + newFile.getAbsolutePath());

        try {
            AtomicBoolean execute = new AtomicBoolean(sp.getForce() == SavePoint.ForceOption.YES);
            if(sp.getForce() == SavePoint.ForceOption.INTERACTIVE){
                Semaphore semaphore = new Semaphore(0);
                Platform.runLater(() -> {
                    Alert a = new Alert(Alert.AlertType.CONFIRMATION);
                    a.setTitle("Overwrite proof file");
                    a.setContentText("Overwrite existing proof file \"" + sp.getName()+"\" (line "+ sp.getLineNumber() +") ?");
                    Optional<ButtonType> buttonType = a.showAndWait();
                    if(buttonType.isPresent() && buttonType.get() == ButtonType.OK){
                        execute.set(true);
                    }
                    semaphore.release();
                });
                semaphore.acquire();
            }

            if(execute.get())
                interpreter.getSelectedNode().getData().getProof().saveToFile(newFile);
                KeyPersistentFacade.write(interpreter.getCurrentState(), new FileWriter(sp.getPersistedStateFile(newFile)));
            System.out.println();

        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        } catch (JAXBException e) {
            e.printStackTrace();
        }
    }



}







