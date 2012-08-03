package de.uka.ilkd.keyabs.gui;

import de.uka.ilkd.key.gui.AbstractWindowUserInterface;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.init.ABSInitConfig;
import de.uka.ilkd.keyabs.init.ABSProblemInitializer;

public class ABSWindowUserInterface extends AbstractWindowUserInterface<ABSServices, ABSInitConfig> {

    public ABSWindowUserInterface(MainWindow mainWindow) {
        super(mainWindow);
    }

    @Override
    public ABSProblemInitializer createProblemInitializer() {
        return new ABSProblemInitializer(this, getMediator().getProfile(),
                getMediator().getProfile()
                        .createServices(new KeYRecoderExcHandler()), true, this);
    }
}
