import ApiService from "@/services/api";
import Home from "@/views/Home.vue";
import Profile from "@/views/Profile.vue";
import SignIn from "@/views/SignIn.vue";
import SignUp from "@/views/SignUp.vue";
import Call from "@/views/Call.vue";
import _ from "lodash";
import Vue from "vue";
import VueRouter, { RouteConfig } from "vue-router";

Vue.use(VueRouter);

const routes: Array<RouteConfig> = [
  {
    path: "/signin",
    name: "SignIn",
    component: SignIn
  },
  {
    path: "/signup",
    name: "SignUp",
    component: SignUp
  },
  {
    path: "/",
    name: "Home",
    component: Home
  },
  {
    path: "/profile",
    name: "Profile",
    component: Profile
  },
  {
    path: "/invitation",
    name: "Invitations",
    component: () =>
      import(/* webpackChunkName: "admin" */ "@/views/Invitations.vue")
  },
  {
    path: "/invitation/send",
    name: "SendInvitations",
    component: () =>
      import(/* webpackChunkName: "admin" */ "@/views/SendInvitations.vue")
  },
  {
    path: "/admin",
    name: "Admin",
    component: () => import(/* webpackChunkName: "admin" */ "@/views/Admin.vue")
  },
  {
    path: "/callTest",
    name: "CallTest",
    component: Call
  }
];

const router = new VueRouter({
  mode: "history",
  base: process.env.BASE_URL,
  routes
});

router.beforeEach((to, from, next) => {
  if (!_.includes(["SignIn", "SignUp"], to.name) && !ApiService.signedIn()) {
    next({ name: "SignIn" });
  } else {
    next();
  }
});

export default router;
