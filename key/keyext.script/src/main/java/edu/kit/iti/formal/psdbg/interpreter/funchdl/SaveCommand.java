package edu.kit.iti.formal.psdbg.interpreter.funchdl;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.SavePoint;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import edu.kit.iti.formal.psdbg.storage.KeyPersistentFacade;
import lombok.Getter;
import lombok.Setter;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import javax.annotation.Nullable;
import javax.swing.*;
import javax.xml.bind.JAXBException;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Optional;
import java.util.concurrent.Semaphore;
import java.util.concurrent.atomic.AtomicBoolean;

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
                SwingUtilities.invokeLater(() -> {
                    int c = JOptionPane.showConfirmDialog(null,
                            "Overwrite existing proof file \"" + sp.getName()+"\" (line "+ sp.getLineNumber() +")",
                            "Overwrite proof file",
                            JOptionPane.OK_CANCEL_OPTION);
                    if(c==JOptionPane.OK_OPTION){
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

        } catch (IOException | InterruptedException | JAXBException e) {
            e.printStackTrace();
        }
    }
}







