package se.gu.svanefalk.testgeneration.core.concurrency.capsules;

import se.gu.svanefalk.testgeneration.core.concurrency.monitor.ICapsuleMonitor;

public interface ICapsule {

    void addController(CapsuleController controller);

    void addMonitor(ICapsuleMonitor capsuleMonitor);

    void doWork();

    CapsuleController getController();

    void terminate();
}
