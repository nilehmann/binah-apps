// Polyfills
import "core-js/stable";
import "regenerator-runtime/runtime";

import "mutationobserver-shim";

// Introspect types
import "reflect-metadata";

// Vue setup
import Vue from "vue";
import App from "./App.vue";
import IconButton from "./components/IconButton.vue";
import "./plugins/bootstrap-vue";
import "./plugins/vue-fontawesome";

Vue.config.productionTip = false;
Vue.component("icon-button", IconButton);

new App().$mount("#app");
