"use strict";
// EBMC Worker
var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {
    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
};
/// <reference path='ebmc-interface.ts'/>
importScripts("ebmc-interface.js");
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
class EbmcWorkerMessage {
    constructor() {
        this.kind = "";
    }
}
function workerResponse(message) {
    console.log("worker: response ", message.kind);
    postMessage(message);
}
Module['onRuntimeInitialized'] = function () {
    return __awaiter(this, void 0, void 0, function* () {
        workerResponse({ kind: "Ready" });
    });
};
function workerListener(event) {
    return __awaiter(this, void 0, void 0, function* () {
        console.log("worker: received ", event.data);
        switch (event.data.kind) {
            case "Version":
                {
                    let version = yield ebmcVersion();
                    workerResponse({ kind: "Version", text: version });
                }
                break;
            case "Sleep":
                workerResponse({ kind: "Sleeping", text: "sleeping" });
                yield sleep(3000); // 3s
                workerResponse({ kind: "Sleep", text: "done sleeping" });
                break;
            case "Properties":
                {
                    let result = yield ebmcProperties(event.data.text);
                    workerResponse({
                        kind: "Properties",
                        properties: result.properties,
                        errors: result.errors,
                        stdout: result.stdout,
                        stderr: result.stderr
                    });
                }
                break;
            case "Verify":
                {
                    let result = yield ebmcVerify(event.data.bound);
                    workerResponse({
                        kind: "Verify",
                        properties: result.properties,
                        stdout: result.stdout,
                        stderr: result.stderr
                    });
                }
                break;
            default:
                console.log("worker: unknown message kind ", event.data.kind);
        }
    });
}
addEventListener('message', workerListener);
