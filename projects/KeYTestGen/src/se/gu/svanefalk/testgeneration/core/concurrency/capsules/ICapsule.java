package se.gu.svanefalk.testgeneration.core.concurrency.capsules;

import se.gu.svanefalk.testgeneration.core.concurrency.monitor.ICapsuleMonitor;

public interface ICapsule {

    void doWork();

    void addMonitor(ICapsuleMonitor capsuleMonitor);

    void addController(CapsuleController controller);

    CapsuleController getController();

    void terminate();
}
