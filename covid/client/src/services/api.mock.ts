import {
  Invitation,
  InvitationInsert,
  Room,
  RoomData,
  User,
  UserData,
  UserSignUp
} from "@/models";

function delay(ms = 1000) {
  if (process.env.NODE_ENV === "development") {
    return new Promise(resolve => setTimeout(resolve, ms));
  } else {
    return Promise.resolve();
  }
}

const INVITATION: Invitation = {
  id: 1,
  emailAddress: "charlie@hba.org",
  firstName: "Charlie",
  lastName: "Papazian",
  institution: "Home Brewers Association",
  accepted: false
};

const ROOMS: { [id: string]: Room } = {
  1: {
    id: 1,
    name: "Green Room",
    capacity: 8,
    zoomLink: "https://meet.jit.si/109283740293847",
    color: "#00ff00",
    topic: "Stuffs"
  },
  2: {
    id: 2,
    name: "Red Room",
    capacity: 5,
    zoomLink: "https://meet.jit.si/018471092384710",
    color: "#ff0000",
    topic: ""
  },
  3: {
    id: 3,
    name: "Blue Room",
    capacity: 10,
    zoomLink: "https://meet.jit.si/102389471203487",
    color: "#0000ff",
    topic: ""
  }
};

const USERS: { [id: string]: User } = {
  1: {
    id: 1,
    photoURL:
      "https://upload.wikimedia.org/wikipedia/commons/thumb/7/77/Avatar_cat.png/120px-Avatar_cat.png",
    displayName: "Charlie Papazian",
    institution: "Homebrewers",
    pronouns: "",
    bio: "",
    website: "",
    level: "organizer",
    room: "1"
    // room: null
  },
  2: {
    id: 2,
    photoURL: null,
    displayName: "Beerhunter",
    institution: "Beer",
    pronouns: "",
    bio: "",
    website: "",
    level: "atendee",
    room: "1"
  },
  3: {
    id: 3,
    photoURL: null,
    displayName: "Natalie Cilurzo",
    institution: "Russian River",
    pronouns: "",
    bio: "",
    website: "",
    level: "attendee",
    room: "2"
  },
  4: {
    id: 4,
    photoURL: null,
    displayName: "Vinnie Cilurzo",
    institution: "Russina River",
    pronouns: "",
    bio: "",
    website: "",
    level: "atendee",
    room: "2"
  },
  5: {
    id: 5,
    photoURL: null,
    displayName: "Greg Koch",
    institution: "Stone Brewing",
    pronouns: "",
    bio: "",
    website: "",
    level: "atendee",
    room: "3"
  },
  6: {
    id: 6,
    photoURL: null,
    displayName: "Dominic",
    institution: "Stone Brewing",
    pronouns: "",
    bio: "",
    website: "",
    level: "atendee",
    room: "3"
  },
  7: {
    id: 7,
    photoURL: null,
    displayName: "Steve Wagner",
    institution: "Stone Brewing",
    pronouns: "",
    bio: "",
    website: "",
    level: "atendee",
    room: "3"
  }
};

const SESSION_USER_ID = "1";

class ApiService {
  constructor(private accessToken: string | null) {}

  get sessionUserId(): string | null {
    if (!this.accessToken) {
      return null;
    }
    return SESSION_USER_ID;
  }

  // Auth

  async signIn(emailAddress: string, password: string): Promise<User> {
    await delay();
    this.accessToken = "accessToken";
    return USERS[SESSION_USER_ID];
  }

  async signUp(data: UserSignUp): Promise<User> {
    await delay();
    return USERS[SESSION_USER_ID];
  }

  signedIn() {
    return this.accessToken !== null;
  }

  signOut() {
    this.accessToken = null;
    return Promise.resolve();
  }

  // Invitations

  async getInvitation(param: string): Promise<Invitation> {
    await delay();
    return INVITATION;
  }

  sendInvitations(invitations: InvitationInsert[]): Promise<string[]> {
    return Promise.reject("Not implemented");
  }

  getInvitations(): Promise<Invitation[]> {
    return Promise.reject("Not implemented");
  }

  // Users

  async user(userId: number): Promise<User> {
    await delay();
    const user = USERS[SESSION_USER_ID];
    if (user) {
      return user;
    } else {
      return this.errorResponse(404);
    }
  }

  async users(): Promise<User[]> {
    await delay();
    return Object.values(USERS);
  }

  async updateUserDataMe(data: UserData): Promise<User> {
    await delay();
    const user = USERS[SESSION_USER_ID];
    if (user) {
      return { ...user, ...data };
    } else {
      return this.errorResponse(404);
    }
  }

  // Rooms

  rooms(): Promise<Room[]> {
    return Promise.resolve(Object.values(ROOMS));
  }

  updateRoom(id: number, data: RoomData): Promise<Room> {
    return Promise.resolve({ ...data, id });
  }

  updateRooms(updates: Room[], inserts: RoomData[]): Promise<number[]> {
    return Promise.reject("Not implemented");
  }

  joinRoom(roomId: string): Promise<string> {
    return Promise.resolve(ROOMS[roomId].zoomLink);
  }

  leaveRoom(): Promise<void> {
    return Promise.reject("Not implemented");
  }

  // Files

  async uploadFile(file: File, code?: string): Promise<string> {
    await delay();
    return Promise.resolve(
      "https://upload.wikimedia.org/wikipedia/commons/thumb/7/77/Avatar_cat.png/120px-Avatar_cat.png"
    );
  }

  // Errors

  errorResponse(status: number): Promise<any> {
    return Promise.reject({ response: { status: status } });
  }
}

export default new ApiService("accessToken");
