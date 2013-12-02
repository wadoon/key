package com.csvanefalk.keytestgen.core.concurrency.monitor;

import com.csvanefalk.keytestgen.core.concurrency.capsules.ICapsule;

public interface ICapsuleMonitor {

    void doNotify(ICapsule source, IMonitorEvent event);
}
