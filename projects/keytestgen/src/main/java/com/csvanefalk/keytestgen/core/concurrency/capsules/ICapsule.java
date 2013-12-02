package com.csvanefalk.keytestgen.core.concurrency.capsules;

import com.csvanefalk.keytestgen.core.concurrency.monitor.ICapsuleMonitor;

public interface ICapsule {

    void addController(CapsuleController controller);

    void addMonitor(ICapsuleMonitor capsuleMonitor);

    void doWork();

    CapsuleController getController();

    void terminate();
}
