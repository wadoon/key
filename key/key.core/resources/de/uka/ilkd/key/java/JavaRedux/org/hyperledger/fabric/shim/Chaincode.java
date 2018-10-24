/*
Copyright IBM Corp. All Rights Reserved.

SPDX-License-Identifier: Apache-2.0
*/

package org.hyperledger.fabric.shim;

import java.util.HashMap;
import java.util.Map;


/**
 * Defines methods that all chaincodes must implement.
 */
public interface Chaincode {
    /**
     * Called during an instantiate transaction after the container has been
     * established, allowing the chaincode to initialize its internal data.
     */
    public Response init(ChaincodeStub stub);

    /**
     * Called for every Invoke transaction. The chaincode may change its state
     * variables.
     */
    public Response invoke(ChaincodeStub stub);

    public static class Response {

        private final Status status;
        private final String message;
        private final byte[] payload;

        public Response(Status status, String message, byte[] payload) {
            this.status = status;
            this.message = message;
            this.payload = payload;
        }

        public Status getStatus() {
            return status;
        }

        public String getMessage() {
            return message;
        }

        public byte[] getPayload() {
            return payload;
        }

        public enum Status {
            SUCCESS(200),
            INTERNAL_SERVER_ERROR(500);


            private final int code;

            private Status(int code) {
                this.code = code;
            }

            public int getCode() {
                return code;
            }

        }

    }
}
