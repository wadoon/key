import org.junit.Assert;
import org.key_project.ui.interactionlog.InteractionLogFacade;
import org.key_project.ui.interactionlog.model.InteractionLog;

import javax.xml.bind.JAXBException;
import java.io.File;
import java.io.IOException;

/**
 *
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public class InteractionLogFacadeTest {
    @org.junit.Test
    public void storeAndReadInteractionLogEmpty() throws IOException, JAXBException {
        InteractionLog il = new InteractionLog();
        File file = File.createTempFile("interaction_log", "xml");
        InteractionLogFacade.storeInteractionLog(il, file);
        Assert.assertTrue(file.exists());
        InteractionLog readIl = InteractionLogFacade.readInteractionLog(file);
        Assert.assertEquals(0, readIl.getInteractions().size());
    }
}