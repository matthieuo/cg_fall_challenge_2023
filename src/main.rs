use std::{io, fmt, cmp};
use std::collections::{HashSet, VecDeque, HashMap};

macro_rules! parse_input {
    ($x:expr, $t:ident) => ($x.trim().parse::<$t>().unwrap())
}

const MAX_SCANS: usize = 10;
const MAX_CREATURES: usize = 22;
const GRID_MAX_X: usize = 100;
const GRID_MAX_Y: usize = 100;

const BOARD_MAX_X: usize = 10000;
const BOARD_MAX_Y: usize = 10000;

fn go_dir(dir: &RadarDir) -> Point {
    match dir {
	RadarDir::BL => Point {x:0,y:10000},
	RadarDir::TL => Point {x:0,y:0},
	RadarDir::BR => Point {x:10000, y:10000},
	RadarDir::TR => Point {x:10000, y:0},
    }
}


    
#[derive(Debug, Clone, Copy)]
struct Point { 
    x:i32,
    y:i32,
}

impl fmt::Display for Point {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
	fmt.write_str(&format!("({}, {})",self.x,self.y))?;
        Ok(())
    }
}

impl Point {
    fn dist(p1: &Point, p2: &Point) -> f64 {
	let dx = f64::from(p1.x - p2.x);
	let dy = f64::from(p1.y - p2.y);
	(dx * dx + dy * dy).sqrt()
    }
    fn gridify(&self) -> Point {
	Point {x:(self.x as f32/GRID_MAX_X as f32).round() as i32, y:(self.y as f32/GRID_MAX_Y as f32).round() as i32}
    }
}


#[derive(Debug, PartialEq, Clone, Copy)]
enum MapLocation {
    T, // tout en haut
    H, // en haut
    M, // millieu
    B, // bas
    Mo, // monster
}

impl MapLocation {
    fn to_min_max_pts(ml: MapLocation) -> (Point, Point) {
	match ml {
	    MapLocation::T => (Point {x:0,y:0}, Point {x:BOARD_MAX_X as i32,y:2500}),
	    MapLocation::H => (Point {x:0,y:2500}, Point {x:BOARD_MAX_X as i32,y:5000}),
	    MapLocation::M => (Point {x:0,y:5000}, Point {x:BOARD_MAX_X as i32,y:7500}),
	    MapLocation::B => (Point {x:0,y:7500}, Point {x:BOARD_MAX_X as i32,y:10000}),
	    MapLocation::Mo => (Point {x:0,y:2500}, Point {x:BOARD_MAX_X as i32,y:10000}),
	}
    }
}

#[derive(Debug, Clone, Copy)]
enum RadarDir {
    TL, // : la créature est en haut à gauche du drone.
    TR, // : la créature est en haut à droite du drone.
    BR, // : la créature est en bas à droite du drone.
    BL, // : la créature est en bas à gauche du drone.
}

#[derive(Debug, Copy, Clone)]
struct FishDetail {
    color: i32,
    fish_type: i32,
}
impl FishDetail {
    fn get_zone(&self) -> MapLocation {
	match self.fish_type {
	    0 => MapLocation::H,
	    1 => MapLocation::M,
	    2 => MapLocation::B,
	    _ => MapLocation::Mo,
	}
    }
}

#[derive(Debug)]
struct Fish {
    fish_id: i32,
    pos: Point,
    speed: Point,
    detail: FishDetail,
}

#[derive(Debug)]
struct RadarBlip {
    fish_id: i32,
    fish_detail: FishDetail,
    dir: RadarDir,
}

#[derive(Debug)]
struct Drone {
    drone_id: i32,
    pos: Point,
    emergency: bool,
    battery: i32,
    scans: Vec<i32>,
    radars: Option<Vec<RadarBlip>>,
}

impl Drone {
    fn where_i_am(&self) -> MapLocation {
	if self.pos.y < 2500 {
           return MapLocation::T;
	}
	else if  self.pos.y < 5000 {
            return MapLocation::H;
	}
	else if self.pos.y < 7500 {
            return MapLocation::M;
	}
	else {
            return MapLocation::B;
	}
    }
}

#[derive(Debug)]
struct InputlBoard {
    my_score: i32,
    opp_score: i32,
    fish_details: HashMap<i32, FishDetail>,
    my_scans: Vec<i32>,
    opp_scans: Vec<i32>,

    my_drones: Vec<Drone>,
    opp_drones: Vec<Drone>,
    
    
}


enum Action { 
    MOVE(Point, bool), 
    WAIT(bool),
}


impl fmt::Display for Action {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
  	match self {
	    Action::MOVE(p, l) => fmt.write_str(&format!("MOVE {} {} {}",p.x,p.y,*l as i32))?,
	    Action::WAIT(l) => fmt.write_str(&format!("WAIT {}", l))?,
	}
        Ok(())
    }
}



#[derive(Debug, Copy, Clone)]
struct GridElem {
    creatures_proba :[f32; MAX_CREATURES],

    
}
#[derive(Debug)]
struct GridApprox {
    grid: [[GridElem; GRID_MAX_X]; GRID_MAX_Y],
    grid_sliced: [Option<GridSlice>; MAX_CREATURES],
    
}

#[derive(Debug, Clone, Copy)]
/// points are note in the gridified space !!
struct GridSlice {
    p_min: Point,
    p_max: Point,

}

impl GridSlice {
    /// num elems for the gridified slice
    fn num_elems(&self) -> i32 {
	let min_y = self.p_min.gridify().y as usize;
	let min_x = self.p_min.gridify().x as usize;
	let max_y = self.p_max.gridify().y as usize;
	let max_x = self.p_max.gridify().x as usize;
	((max_x - min_x)*(max_y - min_y)) as i32
    }

    fn from_tuple(pts: (Point, Point)) -> GridSlice {
	let (p_min, p_max) = pts;
	GridSlice {p_min, p_max}
	
    }

    fn intersec(&self, gs:GridSlice) -> GridSlice {
	let min_y1 = self.p_min.y as usize;
	let min_x1 = self.p_min.x as usize;
	let max_y1 = self.p_max.y as usize;
	let max_x1 = self.p_max.x as usize;

	let min_y2 = gs.p_min.y as usize;
	let min_x2 = gs.p_min.x as usize;
	let max_y2 = gs.p_max.y as usize;
	let max_x2 = gs.p_max.x as usize;

	let min_x_n = cmp::max(min_x1, min_x2);
	let max_x_n = cmp::min(max_x1, max_x2);
	let min_y_n = cmp::max(min_y1, min_y2);
	let max_y_n = cmp::min(max_y1, max_y2);

	GridSlice {p_min: Point {x:min_x_n as i32, y:min_y_n as i32}, p_max: Point {x:max_x_n as i32, y:max_y_n as i32}}
	
    }

    fn from_radar(d_pos: Point, r_dir: RadarDir) -> GridSlice {
	match r_dir {
	    RadarDir::BL => GridSlice {p_min: Point {x:0,y:d_pos.y}, p_max: Point {x:d_pos.x, y:BOARD_MAX_Y as i32}},
	    RadarDir::BR => GridSlice {p_min: d_pos , p_max: Point {x:BOARD_MAX_X as i32,y:BOARD_MAX_Y as i32}},
	    RadarDir::TL => GridSlice {p_min: Point {x:0,y:0}, p_max: d_pos},
	    RadarDir::TR => GridSlice {p_min: Point {x:d_pos.x, y:0}, p_max: Point {x:BOARD_MAX_X as i32,y:d_pos.y}} ,
	}
    }

    fn from_map_loc(ml: MapLocation) -> GridSlice {
	GridSlice::from_tuple(MapLocation::to_min_max_pts(ml))
    }

    fn center(&self) -> Point {
	Point {x:self.p_min.x + (self.p_max.x - self.p_min.x)/2, y:self.p_min.y + (self.p_max.y - self.p_min.y)/2}
    }
}

impl GridApprox {

    fn update_proba(&mut self, fish_id:i32, gs: &GridSlice) {
	let min_y = gs.p_min.gridify().y as usize;
	let min_x = gs.p_min.gridify().x as usize;
	let max_y = gs.p_max.gridify().y as usize;
	let max_x = gs.p_max.gridify().x as usize;
	
	for i in min_y..max_y {
	    for j in &mut self.grid[i][min_x..max_x] {	
		j.creatures_proba[fish_id as usize] = (1.0)/ gs.num_elems() as f32;
	    }
	}

    }
    
    fn from_input_board(ib:&InputlBoard) -> GridApprox {
	let mut out_g = GridApprox {grid: [[GridElem {creatures_proba:[0.0;MAX_CREATURES]} ; GRID_MAX_X];GRID_MAX_Y], grid_sliced:[None; MAX_CREATURES]};

	/*for (f_id, fd) in ib.fish_details.iter() {
	    	    out_g.update_proba(*f_id, &GridSlice::from_tuple(MapLocation::to_min_max_pts(fd.get_zone())));
	
	}*/
	
	for d in ib.my_drones.iter().chain(ib.opp_drones.iter()) {
	    let pg = d.pos.gridify();
	    out_g.grid[pg.x as usize][pg.y as usize].creatures_proba[d.drone_id as usize] = 1.0;
	}

	//update based on radar
	let mut tab_creat :[Option<GridSlice>; MAX_CREATURES] = [None; MAX_CREATURES];
	eprintln!("{:?}", tab_creat[15]);
	
	for d in ib.my_drones.iter() {
	    for r in d.radars.as_ref().unwrap().iter() {
		let gs_r = GridSlice::from_radar(d.pos, r.dir);
		let gs_f = GridSlice::from_map_loc(r.fish_detail.get_zone());
		let inter = gs_r.intersec(gs_f);

		if r.fish_id == 15 {
		    //eprintln!("did = {}", d.drone_id);
		    //eprintln!("{:?}", gs_r);
		    //eprintln!("{:?}", gs_f);
		    //eprintln!("{:?}", inter);
		}
		if let Some(gs_e) = &mut tab_creat[r.fish_id as usize] {
		    *gs_e = gs_e.intersec(inter);
		}
		else {
		  tab_creat[r.fish_id as usize] = Some(inter);  
		}		
	    }
	}

	eprintln!("fin = {:?}", tab_creat);
	for (f_id, inte) in tab_creat.iter().enumerate() {
	    if let Some(in_f) = inte {
		out_g.update_proba(f_id as i32, in_f);
	    }
	}
	out_g.grid_sliced = tab_creat;
	
	out_g
    }
}



/**
 * Score points by scanning valuable fish faster than your opponent.
 **/
fn main() {

    //let ac = Action::MOVE(Point {x:54, y:44}, true);
	    
    //println!("{}", ac); // MOVE <x> <y> <light (1|0)> | WAIT <light (1|0)>

   

    let mut hash_fish = HashMap::new();
    
    let mut input_line = String::new();
    io::stdin().read_line(&mut input_line).unwrap();
    let creature_count = parse_input!(input_line, i32);
    for _ in 0..creature_count as usize {
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let inputs = input_line.split(" ").collect::<Vec<_>>();
        let creature_id = parse_input!(inputs[0], i32);
        let color = parse_input!(inputs[1], i32);
        let fish_type = parse_input!(inputs[2], i32);
	assert!(creature_id <= 21);
	hash_fish.insert(creature_id, FishDetail {color, fish_type});
    }

    // game loop
    let mut cur_step = 0;
    loop {
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let my_score = parse_input!(input_line, i32);
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let foe_score = parse_input!(input_line, i32);
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
	let mut my_scans = Vec::new();
        let my_scan_count = parse_input!(input_line, i32);
        for _ in 0..my_scan_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let creature_id = parse_input!(input_line, i32);
	    my_scans.push(creature_id);
        }
	let mut opp_scans = Vec::new();
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let foe_scan_count = parse_input!(input_line, i32);
        for _ in 0..foe_scan_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let creature_id = parse_input!(input_line, i32);
	    opp_scans.push(creature_id);
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();

	let mut my_drones= Vec::new();
        let my_drone_count = parse_input!(input_line, i32);
        for _ in 0..my_drone_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let drone_x = parse_input!(inputs[1], i32);
            let drone_y = parse_input!(inputs[2], i32);
            let emergency = parse_input!(inputs[3], i32);
            let battery = parse_input!(inputs[4], i32);
	    my_drones.push(Drone {drone_id:drone_id, pos:Point{x:drone_x,y:drone_y}, emergency:emergency==1,battery:battery,scans:Vec::new(),radars:Some(Vec::new())});
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
	let mut opp_drones= Vec::new();
        let foe_drone_count = parse_input!(input_line, i32);
        for _ in 0..foe_drone_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let drone_x = parse_input!(inputs[1], i32);
            let drone_y = parse_input!(inputs[2], i32);
            let emergency = parse_input!(inputs[3], i32);
            let battery = parse_input!(inputs[4], i32);
	    opp_drones.push(Drone {drone_id:drone_id, pos:Point{x:drone_x,y:drone_y}, emergency:emergency==1,battery:battery,scans:Vec::new(),radars:None});
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let drone_scan_count = parse_input!(input_line, i32);
        for _ in 0..drone_scan_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let creature_id = parse_input!(inputs[1], i32);
	    opp_drones.iter_mut()
		.chain(my_drones.iter_mut())
		.find(|e| e.drone_id == drone_id)
		.unwrap()
		.scans.push(creature_id);
	    
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let visible_creature_count = parse_input!(input_line, i32);
	let mut visible_fishes = Vec::new();
	
        for _ in 0..visible_creature_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let creature_id = parse_input!(inputs[0], i32);
            let creature_x = parse_input!(inputs[1], i32);
            let creature_y = parse_input!(inputs[2], i32);
            let creature_vx = parse_input!(inputs[3], i32);
            let creature_vy = parse_input!(inputs[4], i32);
	    visible_fishes.push(Fish {fish_id:creature_id,pos: Point{x:creature_x, y:creature_y},speed: Point{x:creature_vx, y:creature_vy}, detail: *hash_fish.get(&creature_id).unwrap()});
        }
        let mut input_line = String::new();
        io::stdin().read_line(&mut input_line).unwrap();
        let radar_blip_count = parse_input!(input_line, i32);
        for _ in 0..radar_blip_count as usize {
            let mut input_line = String::new();
            io::stdin().read_line(&mut input_line).unwrap();
            let inputs = input_line.split(" ").collect::<Vec<_>>();
            let drone_id = parse_input!(inputs[0], i32);
            let creature_id = parse_input!(inputs[1], i32);
            let radar = inputs[2].trim(); //.to_string();

	    let radar_dir = match radar {
		"BL" => Ok(RadarDir::BL),
		"TL" => Ok(RadarDir::TL),
		"TR" => Ok(RadarDir::TR),
		"BR" => Ok(RadarDir::BR),
		_ => Err("Bad radar direction"),
	    };

	    	    
	    my_drones.iter_mut()
		.find(|e| e.drone_id == drone_id)
		.unwrap()
		.radars.as_mut().unwrap().push(RadarBlip {fish_id:creature_id, dir:radar_dir.unwrap(),fish_detail: *hash_fish.get(&creature_id).unwrap()});
        }
	
	let input_board = InputlBoard {fish_details:hash_fish.clone(), my_scans, opp_scans, my_drones, opp_drones, my_score:my_score, opp_score:foe_score};
	let g_a = GridApprox::from_input_board(&input_board);
	//eprintln!("{:?}", g_a);
	

	for (idx, d) in input_board.my_drones.iter().enumerate() {
	    let mut light = false;
	    
	    let mut target = Point {x:d.pos.x, y:500};
	    
	    if d.scans.len() < 5 {
		let loc = d.where_i_am();
		if d.battery >= 5 && loc != MapLocation::T && (cur_step + idx) % 3 == 0 {
                    light = true;
		}
		
		for rb in d.radars.as_ref().unwrap() {
		    if let Some(_) = input_board.my_scans.iter().find(|e| e == &&rb.fish_id) {
			continue;
		    }
		    if let Some(_) = d.scans.iter().find(|e| e == &&rb.fish_id) {
			continue;
		    }
		    target = go_dir(&rb.dir);
		}

	    }
	    let ac = Action::MOVE(target, light);
	    println!("{}", ac);
	}

	cur_step += 1;
    }
}
