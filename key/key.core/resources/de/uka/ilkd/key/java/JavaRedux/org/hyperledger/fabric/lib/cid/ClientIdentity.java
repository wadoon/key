/*
Copyright IBM Corp. 2017 All Rights Reserved.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
                 http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package org.hyperledger.fabric.lib.cid;

public final class ClientIdentity {

    // GetID returns the ID associated with the invoking identity. This ID
    // is guaranteed to be unique within the MSP.
    /*@ public normal_behaviour
      @ ensures \result != 0;
      @*/
    public static /*@ pure helper @*/ int getID(org.hyperledger.fabric.shim.ChaincodeStub stub);
}
