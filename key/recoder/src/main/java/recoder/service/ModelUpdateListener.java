package recoder.service;

import java.util.EventObject;

public interface ModelUpdateListener {
    void modelUpdating(EventObject paramEventObject);

    void modelUpdated(EventObject paramEventObject);
}
