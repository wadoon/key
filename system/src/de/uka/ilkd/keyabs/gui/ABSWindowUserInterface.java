package de.uka.ilkd.keyabs.gui;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.gui.AbstractWindowUserInterface;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.DefaultABSDLProblemLoader;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.init.ABSInitConfig;
import de.uka.ilkd.keyabs.init.ABSProblemInitializer;

public class ABSWindowUserInterface extends AbstractWindowUserInterface<ABSServices, ABSInitConfig> {

    public ABSWindowUserInterface(MainWindow<ABSServices, ABSInitConfig> mainWindow) {
        super(mainWindow);
    }

    @Override
    public ABSProblemInitializer createProblemInitializer(boolean registerProof) {
        return new ABSProblemInitializer(this, getMediator().getProfile(),
                getMediator().getProfile()
                        .createServices(new KeYRecoderExcHandler()), registerProof, this);
    }

    @Override
    public DefaultProblemLoader<ABSServices, ABSInitConfig> createDefaultProblemLoader(
            File file, List<File> classPath, File bootClassPath,
            KeYMediator<ABSServices, ABSInitConfig> mediator) {
        return new DefaultABSDLProblemLoader(file, classPath, bootClassPath, mediator);
    }
}
