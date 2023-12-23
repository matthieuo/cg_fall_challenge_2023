use std::{io, fmt, iter};
use std::collections::{HashSet, VecDeque, HashMap};

macro_rules! parse_input {
    ($x:expr, $t:ident) => ($x.trim().parse::<$t>().unwrap())
}

const MAX_SCANS: usize = 10;


fn go_dir(dir: &RadarDir) -> Point {
    match dir {
	RadarDir::BL => Point {x:0,y:10000},
	RadarDir::TL => Point {x:0,y:0},
	RadarDir::BR => Point {x:10000, y:10000},
	RadarDir::TR => Point {x:10000, y:0},
    }
}


    
#[derive(Debug)]
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
}


#[derive(Debug, PartialEq)]
enum MapLocation {
    T, // tout en haut
    H, // en haut
    M, // millieu
    B, // bas
}


#[derive(Debug)]
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
		.radars.as_mut().unwrap().push(RadarBlip {fish_id:creature_id, dir:radar_dir.unwrap()});
        }
	
	let input_board = InputlBoard {fish_details:hash_fish.clone(), my_scans, opp_scans, my_drones, opp_drones, my_score:my_score, opp_score:foe_score};
	eprintln!("{:?}", input_board);

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
