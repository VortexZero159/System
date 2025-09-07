"-- https://github.com/LorekeeperZinnia/Dex

--[[
	Dex
	Created by Moon
	Modified for Infinite Yield

	Dex is a debugging suite designed to help the user debug games and find any potential vulnerabilities.
]]

local nodes = {}
local selection

local function missing(t, f, fallback)
	if type(f) == t then return f end
	return fallback
end

local cloneref = missing("function", cloneref, function(...) return ... end)
local service = setmetatable({}, {
	__index = function(self, name)
		self[name] = cloneref(game:GetService(name))
		return self[name]
	end
})

-- prevent environment implosion from references
-- mainly from the executor not having some game properties in their game variable
-- so we gotta use vanilla game
local oldgame = game
local game = workspace.Parent

local EmbeddedModules = {
	Explorer = function()
--[[
	Explorer App Module
	
	The main explorer interface
]]

		-- Common Locals
		local Main,Lib,Apps,Settings -- Main Containers
		local Explorer, Properties, ScriptViewer, Notebook -- Major Apps
		local API,RMD,env,service,plr,create,createSimple -- Main Locals

		local function initDeps(data)
			Main = data.Main
			Lib = data.Lib
			Apps = data.Apps
			Settings = data.Settings

			API = data.API
			RMD = data.RMD
			env = data.env
			service = data.service
			plr = data.plr
			create = data.create
			createSimple = data.createSimple
		end

		local function initAfterMain()
			Explorer = Apps.Explorer
			Properties = Apps.Properties
			ScriptViewer = Apps.ScriptViewer
			Notebook = Apps.Notebook
		end

		local function main()
			local Explorer = {}
			local tree,listEntries,explorerOrders,searchResults,specResults = {},{},{},{},{}
			local expanded
			local entryTemplate,treeFrame,toolBar,descendantAddedCon,descendantRemovingCon,itemChangedCon
			local ffa = game.FindFirstAncestorWhichIsA
			local getDescendants = game.GetDescendants
			local getTextSize = service.TextService.GetTextSize
			local updateDebounce,refreshDebounce = false,false
			local nilNode = {Obj = Instance.new("Folder")}
			local idCounter = 0
			local scrollV,scrollH,clipboard
			local renameBox,renamingNode,searchFunc
			local sortingEnabled,autoUpdateSearch
			local table,math = table,math
			local nilMap,nilCons = {},{}
			local connectSignal = game.DescendantAdded.Connect
			local addObject,removeObject,moveObject = nil,nil,nil

			addObject = function(root)
				if nodes[root] then return end

				local isNil = false
				local rootParObj = ffa(root,"Instance")
				local par = nodes[rootParObj]

				-- Nil Handling
				if not par then
					if nilMap[root] then
						nilCons[root] = nilCons[root] or {
							connectSignal(root.ChildAdded,addObject),
							connectSignal(root.AncestryChanged,moveObject),
						}
						par = nilNode
						isNil = true
					else
						return
					end
				elseif nilMap[rootParObj] or par == nilNode then
					nilMap[root] = true
					nilCons[root] = nilCons[root] or {
						connectSignal(root.ChildAdded,addObject),
						connectSignal(root.AncestryChanged,moveObject),
					}
					isNil = true
				end

				local newNode = {Obj = root, Parent = par}
				nodes[root] = newNode

				-- Automatic sorting if expanded
				if sortingEnabled and expanded[par] and par.Sorted then
					local left,right = 1,#par
					local floor = math.floor
					local sorter = Explorer.NodeSorter
					local pos = (right == 0 and 1)

					if not pos then
						while true do
							if left >= right then
								if sorter(newNode,par[left]) then
									pos = left
								else
									pos = left+1
								end
								break
							end

							local mid = floor((left+right)/2)
							if sorter(newNode,par[mid]) then
								right = mid-1
							else
								left = mid+1
							end
						end
					end

					table.insert(par,pos,newNode)
				else
					par[#par+1] = newNode
					par.Sorted = nil
				end

				local insts = getDescendants(root)
				for i = 1,#insts do
					local obj = insts[i]
					if nodes[obj] then continue end -- Deferred

					local par = nodes[ffa(obj,"Instance")]
					if not par then continue end
					local newNode = {Obj = obj, Parent = par}
					nodes[obj] = newNode
					par[#par+1] = newNode

					-- Nil Handling
					if isNil then
						nilMap[obj] = true
						nilCons[obj] = nilCons[obj] or {
							connectSignal(obj.ChildAdded,addObject),
							connectSignal(obj.AncestryChanged,moveObject),
						}
					end
				end

				if searchFunc and autoUpdateSearch then
					searchFunc({newNode})
				end

				if not updateDebounce and Explorer.IsNodeVisible(par) then
					if expanded[par] then
						Explorer.PerformUpdate()
					elseif not refreshDebounce then
						Explorer.PerformRefresh()
					end
				end
			end

			removeObject = function(root)
				local node = nodes[root]
				if not node then return end

				-- Nil Handling
				if nilMap[node.Obj] then
					moveObject(node.Obj)
					return
				end

				local par = node.Parent
				if par then
					par.HasDel = true
				end

				local function recur(root)
					for i = 1,#root do
						local node = root[i]
						if not node.Del then
							nodes[node.Obj] = nil
							if #node > 0 then recur(node) end
						end
					end
				end
				recur(node)
				node.Del = true
				nodes[root] = nil

				if par and not updateDebounce and Explorer.IsNodeVisible(par) then
					if expanded[par] then
						Explorer.PerformUpdate()
					elseif not refreshDebounce then
						Explorer.PerformRefresh()
					end
				end
			end

			moveObject = function(obj)
				local node = nodes[obj]
				if not node then return end

				local oldPar = node.Parent
				local newPar = nodes[ffa(obj,"Instance")]
				if oldPar == newPar then return end

				-- Nil Handling
				if not newPar then
					if nilMap[obj] then
						newPar = nilNode
					else
						return
					end
				elseif nilMap[newPar.Obj] or newPar == nilNode then
					nilMap[obj] = true
					nilCons[obj] = nilCons[obj] or {
						connectSignal(obj.ChildAdded,addObject),
						connectSignal(obj.AncestryChanged,moveObject),
					}
				end

				if oldPar then
					local parPos = table.find(oldPar,node)
					if parPos then table.remove(oldPar,parPos) end
				end

				node.Id = nil
				node.Parent = newPar

				if sortingEnabled and expanded[newPar] and newPar.Sorted then
					local left,right = 1,#newPar
					local floor = math.floor
					local sorter = Explorer.NodeSorter
					local pos = (right == 0 and 1)

					if not pos then
						while true do
							if left >= right then
								if sorter(node,newPar[left]) then
									pos = left
								else
									pos = left+1
								end
								break
							end

							local mid = floor((left+right)/2)
							if sorter(node,newPar[mid]) then
								right = mid-1
							else
								left = mid+1
							end
						end
					end

					table.insert(newPar,pos,node)
				else
					newPar[#newPar+1] = node
					newPar.Sorted = nil
				end

				if searchFunc and searchResults[node] then
					local currentNode = node.Parent
					while currentNode and (not searchResults[currentNode] or expanded[currentNode] == 0) do
						expanded[currentNode] = true
						searchResults[currentNode] = true
						currentNode = currentNode.Parent
					end
				end

				if not updateDebounce and (Explorer.IsNodeVisible(newPar) or Explorer.IsNodeVisible(oldPar)) then
					if expanded[newPar] or expanded[oldPar] then
						Explorer.PerformUpdate()
					elseif not refreshDebounce then
						Explorer.PerformRefresh()
					end
				end
			end

			Explorer.ViewWidth = 0
			Explorer.Index = 0
			Explorer.EntryIndent = 20
			Explorer.FreeWidth = 32
			Explorer.GuiElems = {}

			Explorer.InitRenameBox = function()
				renameBox = create({{1,"TextBox",{BackgroundColor3=Color3.new(0.17647059261799,0.17647059261799,0.17647059261799),BorderColor3=Color3.new(0.062745101749897,0.51764708757401,1),BorderMode=2,ClearTextOnFocus=false,Font=3,Name="RenameBox",PlaceholderColor3=Color3.new(0.69803923368454,0.69803923368454,0.69803923368454),Position=UDim2.new(0,26,0,2),Size=UDim2.new(0,200,0,16),Text="",TextColor3=Color3.new(1,1,1),TextSize=14,TextXAlignment=0,Visible=false,ZIndex=2}}})

				renameBox.Parent = Explorer.Window.GuiElems.Content.List

				renameBox.FocusLost:Connect(function()
					if not renamingNode then return end

					pcall(function() renamingNode.Obj.Name = renameBox.Text end)
					renamingNode = nil
					Explorer.Refresh()
				end)

				renameBox.Focused:Connect(function()
					renameBox.SelectionStart = 1
					renameBox.CursorPosition = #renameBox.Text + 1
				end)
			end

			Explorer.SetRenamingNode = function(node)
				renamingNode = node
				renameBox.Text = tostring(node.Obj)
				renameBox:CaptureFocus()
				Explorer.Refresh()
			end

			Explorer.SetSortingEnabled = function(val)
				sortingEnabled = val
				Settings.Explorer.Sorting = val
			end

			Explorer.UpdateView = function()
				local maxNodes = math.ceil(treeFrame.AbsoluteSize.Y / 20)
				local maxX = treeFrame.AbsoluteSize.X
				local totalWidth = Explorer.ViewWidth + Explorer.FreeWidth

				scrollV.VisibleSpace = maxNodes
				scrollV.TotalSpace = #tree + 1
				scrollH.VisibleSpace = maxX
				scrollH.TotalSpace = totalWidth

				scrollV.Gui.Visible = #tree + 1 > maxNodes
				scrollH.Gui.Visible = totalWidth > maxX

				local oldSize = treeFrame.Size
				treeFrame.Size = UDim2.new(1,(scrollV.Gui.Visible and -16 or 0),1,(scrollH.Gui.Visible and -39 or -23))
				if oldSize ~= treeFrame.Size then
					Explorer.UpdateView()
				else
					scrollV:Update()
					scrollH:Update()

					renameBox.Size = UDim2.new(0,maxX-100,0,16)

					if scrollV.Gui.Visible and scrollH.Gui.Visible then
						scrollV.Gui.Size = UDim2.new(0,16,1,-39)
						scrollH.Gui.Size = UDim2.new(1,-16,0,16)
						Explorer.Window.GuiElems.Content.ScrollCorner.Visible = true
					else
						scrollV.Gui.Size = UDim2.new(0,16,1,-23)
						scrollH.Gui.Size = UDim2.new(1,0,0,16)
						Explorer.Window.GuiElems.Content.ScrollCorner.Visible = false
					end

					Explorer.Index = scrollV.Index
				end
			end

			Explorer.NodeSorter = function(a,b)
				if a.Del or b.Del then return false end -- Ghost node

				local aClass = a.Class
				local bClass = b.Class
				if not aClass then aClass = a.Obj.ClassName a.Class = aClass end
				if not bClass then bClass = b.Obj.ClassName b.Class = bClass end

				local aOrder = explorerOrders[aClass]
				local bOrder = explorerOrders[bClass]
				if not aOrder then aOrder = RMD.Classes[aClass] and tonumber(RMD.Classes[aClass].ExplorerOrder) or 9999 explorerOrders[aClass] = aOrder end
				if not bOrder then bOrder = RMD.Classes[bClass] and tonumber(RMD.Classes[bClass].ExplorerOrder) or 9999 explorerOrders[bClass] = bOrder end

				if aOrder ~= bOrder then
					return aOrder < bOrder
				else
					local aName,bName = tostring(a.Obj),tostring(b.Obj)
					if aName ~= bName then
						return aName < bName
					elseif aClass ~= bClass then
						return aClass < bClass
					else
						local aId = a.Id if not aId then aId = idCounter idCounter = (idCounter+0.001)%999999999 a.Id = aId end
						local bId = b.Id if not bId then bId = idCounter idCounter = (idCounter+0.001)%999999999 b.Id = bId end
						return aId < bId
					end
				end
			end

			Explorer.Update = function()
				table.clear(tree)
				local maxNameWidth,maxDepth,count = 0,1,1
				local nameCache = {}
				local font = Enum.Font.SourceSans
				local size = Vector2.new(math.huge,20)
				local useNameWidth = Settings.Explorer.UseNameWidth
				local tSort = table.sort
				local sortFunc = Explorer.NodeSorter
				local isSearching = (expanded == Explorer.SearchExpanded)
				local textServ = service.TextService

				local function recur(root,depth)
					if depth > maxDepth then maxDepth = depth end
					depth = depth + 1
					if sortingEnabled and not root.Sorted then
						tSort(root,sortFunc)
						root.Sorted = true
					end
					for i = 1,#root do
						local n = root[i]

						if (isSearching and not searchResults[n]) or n.Del then continue end

						if useNameWidth then
							local nameWidth = n.NameWidth
							if not nameWidth then
								local objName = tostring(n.Obj)
								nameWidth = nameCache[objName]
								if not nameWidth then
									nameWidth = getTextSize(textServ,objName,14,font,size).X
									nameCache[objName] = nameWidth
								end
								n.NameWidth = nameWidth
							end
							if nameWidth > maxNameWidth then
								maxNameWidth = nameWidth
							end
						end

						tree[count] = n
						count = count + 1
						if expanded[n] and #n > 0 then
							recur(n,depth)
						end
					end
				end

				recur(nodes[game],1)

				-- Nil Instances
				if env.getnilinstances then
					if not (isSearching and not searchResults[nilNode]) then
						tree[count] = nilNode
						count = count + 1
						if expanded[nilNode] then
							recur(nilNode,2)
						end
					end
				end

				Explorer.MaxNameWidth = maxNameWidth
				Explorer.MaxDepth = maxDepth
				Explorer.ViewWidth = useNameWidth and Explorer.EntryIndent*maxDepth + maxNameWidth + 26 or Explorer.EntryIndent*maxDepth + 226
				Explorer.UpdateView()
			end

			Explorer.StartDrag = function(offX,offY)
				if Explorer.Dragging then return end
				for i,v in next, selection.List do
					local Obj = v.Obj
					if Obj.Parent == game or Obj:IsA("Player") then
						return
					end
				end
				Explorer.Dragging = true

				local dragTree = treeFrame:Clone()
				dragTree:ClearAllChildren()

				for i,v in pairs(listEntries) do
					local node = tree[i + Explorer.Index]
					if node and selection.Map[node] then
						local clone = v:Clone()
						clone.Active = false
						clone.Indent.Expand.Visible = false
						clone.Parent = dragTree
					end
				end

				local newGui = Instance.new("ScreenGui")
				newGui.DisplayOrder = Main.DisplayOrders.Menu
				dragTree.Parent = newGui
				Lib.ShowGui(newGui)

				local dragOutline = create({
					{1,"Frame",{BackgroundColor3=Color3.new(1,1,1),BackgroundTransparency=1,Name="DragSelect",Size=UDim2.new(1,0,1,0),}},
					{2,"Frame",{BackgroundColor3=Color3.new(1,1,1),BorderSizePixel=0,Name="Line",Parent={1},Size=UDim2.new(1,0,0,1),ZIndex=2,}},
					{3,"Frame",{BackgroundColor3=Color3.new(1,1,1),BorderSizePixel=0,Name="Line",Parent={1},Position=UDim2.new(0,0,1,-1),Size=UDim2.new(1,0,0,1),ZIndex=2,}},
					{4,"Frame",{BackgroundColor3=Color3.new(1,1,1),BorderSizePixel=0,Name="Line",Parent={1},Size=UDim2.new(0,1,1,0),ZIndex=2,}},
					{5,"Frame",{BackgroundColor3=Color3.new(1,1,1),BorderSizePixel=0,Name="Line",Parent={1},Position=UDim2.new(1,-1,0,0),Size=UDim2.new(0,1,1,0),ZIndex=2,}},
				})
				dragOutline.Parent = treeFrame

				local mouse = Main.Mouse or service.Players.LocalPlayer:GetMouse()
				local function move()
					local posX = mouse.X - offX
					local posY = mouse.Y - offY
					dragTree.Position = UDim2.new(0,posX,0,posY)

					for i = 1,#listEntries do
						local entry = listEntries[i]
						if Lib.CheckMouseInGui(entry) then
							dragOutline.Position = UDim2.new(0,entry.Indent.Position.X.Offset-scrollH.Index,0,entry.Position.Y.Offset)
							dragOutline.Size = UDim2.new(0,entry.Size.X.Offset-entry.Indent.Position.X.Offset,0,20)
							dragOutline.Visible = true
							return
						end
					end
					dragOutline.Visible = false
				end
				move()

				local input = service.UserInputService
				local mouseEvent,releaseEvent

				mouseEvent = input.InputChanged:Connect(function(input)
					if input.UserInputType == Enum.UserInputType.MouseMovement or input.UserInputType == Enum.UserInputType.Touch then
						move()
					end
				end)

				releaseEvent = input.InputEnded:Connect(function(input)
					if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
						releaseEvent:Disconnect()
						mouseEvent:Disconnect()
						newGui:Destroy()
						dragOutline:Destroy()
						Explorer.Dragging = false

						for i = 1,#listEntries do
							if Lib.CheckMouseInGui(listEntries[i]) then
								local node = tree[i + Explorer.Index]
								if node then
									if selection.Map[node] then return end
									local newPar = node.Obj
									local sList = selection.List
									for i = 1,#sList do
										local n = sList[i]
										pcall(function() n.Obj.Parent = newPar end)
									end
									Explorer.ViewNode(sList[1])
								end
								break
							end
						end
					end
				end)
			end

			Explorer.NewListEntry = function(index)
				local newEntry = entryTemplate:Clone()
				newEntry.Position = UDim2.new(0,0,0,20*(index-1))

				local isRenaming = false

				newEntry.InputBegan:Connect(function(input)
					local node = tree[index + Explorer.Index]
					if not node or selection.Map[node] or (input.UserInputType ~= Enum.UserInputType.MouseMovement and input.UserInputType ~= Enum.UserInputType.Touch) then return end

					newEntry.Indent.BackgroundColor3 = Settings.Theme.Button
					newEntry.Indent.BorderSizePixel = 0
					newEntry.Indent.BackgroundTransparency = 0
				end)

				newEntry.InputEnded:Connect(function(input)
					local node = tree[index + Explorer.Index]
					if not node or selection.Map[node] or (input.UserInputType ~= Enum.UserInputType.MouseMovement and input.UserInputType ~= Enum.UserInputType.Touch) then return end

					newEntry.Indent.BackgroundTransparency = 1
				end)

				newEntry.MouseButton1Down:Connect(function()

				end)

				newEntry.MouseButton1Up:Connect(function()

				end)

				newEntry.InputBegan:Connect(function(input)
					if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
						local releaseEvent, mouseEvent

						local mouse = Main.Mouse or plr:GetMouse()
						local startX, startY

						if input.UserInputType == Enum.UserInputType.Touch then
							startX = input.Position.X
							startY = input.Position.Y
						else
							startX = mouse.X
							startY = mouse.Y
						end

						local listOffsetX = startX - treeFrame.AbsolutePosition.X
						local listOffsetY = startY - treeFrame.AbsolutePosition.Y

						releaseEvent = service.UserInputService.InputEnded:Connect(function(input)
							if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
								releaseEvent:Disconnect()
								mouseEvent:Disconnect()
							end
						end)

						mouseEvent = service.UserInputService.InputChanged:Connect(function(input)
							if input.UserInputType == Enum.UserInputType.MouseMovement or input.UserInputType == Enum.UserInputType.Touch then
								local currentX, currentY

								if input.UserInputType == Enum.UserInputType.Touch then
									currentX = input.Position.X
									currentY = input.Position.Y
								else
									currentX = mouse.X
									currentY = mouse.Y
								end

								local deltaX = currentX - startX
								local deltaY = currentY - startY
								local dist = math.sqrt(deltaX^2 + deltaY^2)

								if dist > 5 then
									releaseEvent:Disconnect()
									mouseEvent:Disconnect()
									isRenaming = false
									Explorer.StartDrag(listOffsetX, listOffsetY)
								end
							end
						end)
					end
				end)

				newEntry.MouseButton2Down:Connect(function()

				end)

				newEntry.Indent.Expand.InputBegan:Connect(function(input)
					local node = tree[index + Explorer.Index]
					if not node or (input.UserInputType ~= Enum.UserInputType.MouseMovement and input.UserInputType ~= Enum.UserInputType.Touch) then return end

					if input.UserInputType == Enum.UserInputType.Touch then
						Explorer.MiscIcons:DisplayByKey(newEntry.Indent.Expand.Icon, expanded[node] and "Collapse_Over" or "Expand_Over")
					elseif input.UserInputType == Enum.UserInputType.MouseMovement then
						Explorer.MiscIcons:DisplayByKey(newEntry.Indent.Expand.Icon, expanded[node] and "Collapse_Over" or "Expand_Over")
					end
				end)

				newEntry.Indent.Expand.InputEnded:Connect(function(input)
					local node = tree[index + Explorer.Index]
					if not node or (input.UserInputType ~= Enum.UserInputType.MouseMovement and input.UserInputType ~= Enum.UserInputType.Touch) then return end

					if input.UserInputType == Enum.UserInputType.Touch then
						Explorer.MiscIcons:DisplayByKey(newEntry.Indent.Expand.Icon, expanded[node] and "Collapse" or "Expand")
					elseif input.UserInputType == Enum.UserInputType.MouseMovement then
						Explorer.MiscIcons:DisplayByKey(newEntry.Indent.Expand.Icon, expanded[node] and "Collapse" or "Expand")
					end
				end)

				newEntry.Indent.Expand.MouseButton1Down:Connect(function()
					local node = tree[index + Explorer.Index]
					if not node or #node == 0 then return end

					expanded[node] = not expanded[node]
					Explorer.Update()
					Explorer.Refresh()
				end)

				newEntry.Parent = treeFrame
				return newEntry
			end

			Explorer.Refresh = function()
				local maxNodes = math.max(math.ceil((treeFrame.AbsoluteSize.Y) / 20), 0)	
				local renameNodeVisible = false
				local isa = game.IsA

				for i = 1,maxNodes do
					local entry = listEntries[i]
					if not listEntries[i] then entry = Explorer.NewListEntry(i) listEntries[i] = entry Explorer.ClickSystem:Add(entry) end

					local node = tree[i + Explorer.Index]
					if node then
						local obj = node.Obj
						local depth = Explorer.EntryIndent*Explorer.NodeDepth(node)

						entry.Visible = true
						entry.Position = UDim2.new(0,-scrollH.Index,0,entry.Position.Y.Offset)
						entry.Size = UDim2.new(0,Explorer.ViewWidth,0,20)
						entry.Indent.EntryName.Text = tostring(node.Obj)
						entry.Indent.Position = UDim2.new(0,depth,0,0)
						entry.Indent.Size = UDim2.new(1,-depth,1,0)

						entry.Indent.EntryName.TextTruncate = (Settings.Explorer.UseNameWidth and Enum.TextTruncate.None or Enum.TextTruncate.AtEnd)

						Explorer.MiscIcons:DisplayExplorerIcons(entry.Indent.Icon, obj.ClassName)

						if selection.Map[node] then
							entry.Indent.BackgroundColor3 = Settings.Theme.ListSelection
							entry.Indent.BorderSizePixel = 0
							entry.Indent.BackgroundTransparency = 0
						else
							if Lib.CheckMouseInGui(entry) then
								entry.Indent.BackgroundColor3 = Settings.Theme.Button
							else
								entry.Indent.BackgroundTransparency = 1
							end
						end

						if node == renamingNode then
							renameNodeVisible = true
							renameBox.Position = UDim2.new(0,depth+25-scrollH.Index,0,entry.Position.Y.Offset+2)
							renameBox.Visible = true
						end

						if #node > 0 and expanded[node] ~= 0 then
							if Lib.CheckMouseInGui(entry.Indent.Expand) then
								Explorer.MiscIcons:DisplayByKey(entry.Indent.Expand.Icon, expanded[node] and "Collapse_Over" or "Expand_Over")
							else
								Explorer.MiscIcons:DisplayByKey(entry.Indent.Expand.Icon, expanded[node] and "Collapse" or "Expand")
							end
							entry.Indent.Expand.Visible = true
						else
							entry.Indent.Expand.Visible = false
						end
					else
						entry.Visible = false
					end
				end

				if not renameNodeVisible then
					renameBox.Visible = false
				end

				for i = maxNodes+1, #listEntries do
					Explorer.ClickSystem:Remove(listEntries[i])
					listEntries[i]:Destroy()
					listEntries[i] = nil
				end
			end

			Explorer.PerformUpdate = function(instant)
				updateDebounce = true
				Lib.FastWait(not instant and 0.1)
				if not updateDebounce then return end
				updateDebounce = false
				if not Explorer.Window:IsVisible() then return end
				Explorer.Update()
				Explorer.Refresh()
			end

			Explorer.ForceUpdate = function(norefresh)
				updateDebounce = false
				Explorer.Update()
				if not norefresh then Explorer.Refresh() end
			end

			Explorer.PerformRefresh = function()
				refreshDebounce = true
				Lib.FastWait(0.1)
				refreshDebounce = false
				if updateDebounce or not Explorer.Window:IsVisible() then return end
				Explorer.Refresh()
			end

			Explorer.IsNodeVisible = function(node)
				if not node then return end

				local curNode = node.Parent
				while curNode do
					if not expanded[curNode] then return false end
					curNode = curNode.Parent
				end
				return true
			end

			Explorer.NodeDepth = function(node)
				local depth = 0

				if node == nilNode then
					return 1
				end

				local curNode = node.Parent
				while curNode do
					if curNode == nilNode then depth = depth + 1 end
					curNode = curNode.Parent
					depth = depth + 1
				end
				return depth
			end

			Explorer.SetupConnections = function()
				if descendantAddedCon then descendantAddedCon:Disconnect() end
				if descendantRemovingCon then descendantRemovingCon:Disconnect() end
				if itemChangedCon then itemChangedCon:Disconnect() end

				if Main.Elevated then
					descendantAddedCon = game.DescendantAdded:Connect(addObject)
					descendantRemovingCon = game.DescendantRemoving:Connect(removeObject)
				else
					descendantAddedCon = game.DescendantAdded:Connect(function(obj) pcall(addObject,obj) end)
					descendantRemovingCon = game.DescendantRemoving:Connect(function(obj) pcall(removeObject,obj) end)
				end

				if Settings.Explorer.UseNameWidth then
					itemChangedCon = game.ItemChanged:Connect(function(obj,prop)
						if prop == "Parent" and nodes[obj] then
							moveObject(obj)
						elseif prop == "Name" and nodes[obj] then
							nodes[obj].NameWidth = nil
						end
					end)
				else
					itemChangedCon = game.ItemChanged:Connect(function(obj,prop)
						if prop == "Parent" and nodes[obj] then
							moveObject(obj)
						end
					end)
				end
			end

			Explorer.ViewNode = function(node)
				if not node then return end

				Explorer.MakeNodeVisible(node)
				Explorer.ForceUpdate(true)
				local visibleSpace = scrollV.VisibleSpace

				for i,v in next,tree do
					if v == node then
						local relative = i - 1
						if Explorer.Index > relative then
							scrollV.Index = relative
						elseif Explorer.Index + visibleSpace - 1 <= relative then
							scrollV.Index = relative - visibleSpace + 2
						end
					end
				end

				scrollV:Update() Explorer.Index = scrollV.Index
				Explorer.Refresh()
			end

			Explorer.ViewObj = function(obj)
				Explorer.ViewNode(nodes[obj])
			end

			Explorer.MakeNodeVisible = function(node,expandRoot)
				if not node then return end

				local hasExpanded = false

				if expandRoot and not expanded[node] then
					expanded[node] = true
					hasExpanded = true
				end

				local currentNode = node.Parent
				while currentNode do
					hasExpanded = true
					expanded[currentNode] = true
					currentNode = currentNode.Parent
				end

				if hasExpanded and not updateDebounce then
					coroutine.wrap(Explorer.PerformUpdate)(true)
				end
			end

			Explorer.ShowRightClick = function(MousePos)
				local Mouse = MousePos or Main.Mouse
				local context = Explorer.RightClickContext
				local absoluteSize = context.Gui.AbsoluteSize
				context.MaxHeight = (absoluteSize.Y <= 600 and (absoluteSize.Y - 40)) or nil
				context:Clear()

				local sList = selection.List
				local sMap = selection.Map
				local emptyClipboard = #clipboard == 0
				local presentClasses = {}
				local apiClasses = API.Classes

				for i = 1, #sList do
					local node = sList[i]
					local class = node.Class
					local obj = node.Obj

					if not presentClasses.isViableDecompileScript then
						presentClasses.isViableDecompileScript = env.isViableDecompileScript(obj)
					end
					if not class then
						class = obj.ClassName
						node.Class = class
					end

					local curClass = apiClasses[class]
					while curClass and not presentClasses[curClass.Name] do
						presentClasses[curClass.Name] = true
						curClass = curClass.Superclass
					end
				end

				context:AddRegistered("CUT")
				context:AddRegistered("COPY")
				context:AddRegistered("PASTE", emptyClipboard)
				context:AddRegistered("DUPLICATE")
				context:AddRegistered("DELETE")
				context:AddRegistered("RENAME", #sList ~= 1)

				context:AddDivider()
				context:AddRegistered("GROUP")
				context:AddRegistered("UNGROUP")
				context:AddRegistered("SELECT_CHILDREN")
				context:AddRegistered("JUMP_TO_PARENT")
				context:AddRegistered("EXPAND_ALL")
				context:AddRegistered("COLLAPSE_ALL")

				context:AddDivider()

				if expanded == Explorer.SearchExpanded then context:AddRegistered("CLEAR_SEARCH_AND_JUMP_TO") end
				if env.setclipboard then context:AddRegistered("COPY_PATH") end
				context:AddRegistered("INSERT_OBJECT")
				-- context:AddRegistered("SAVE_INST")
				-- context:AddRegistered("CALL_FUNCTION")
				-- context:AddRegistered("VIEW_CONNECTIONS")
				-- context:AddRegistered("GET_REFERENCES")
				-- context:AddRegistered("VIEW_API")

				context:QueueDivider()

				if presentClasses["BasePart"] or presentClasses["Model"] then
					context:AddRegistered("TELEPORT_TO")
					context:AddRegistered("VIEW_OBJECT")
				end
				if presentClasses["Tween"] then context:AddRegistered("PLAY_TWEEN") end
				if presentClasses["Animation"] then
					context:AddRegistered("LOAD_ANIMATION")
					context:AddRegistered("STOP_ANIMATION")
				end

				if presentClasses["TouchTransmitter"] then context:AddRegistered("FIRE_TOUCHTRANSMITTER", firetouchinterest == nil) end
				if presentClasses["ClickDetector"] then context:AddRegistered("FIRE_CLICKDETECTOR", fireclickdetector == nil) end
				if presentClasses["ProximityPrompt"] then context:AddRegistered("FIRE_PROXIMITYPROMPT", fireproximityprompt == nil) end

				if presentClasses["Player"] then context:AddRegistered("SELECT_CHARACTER")context:AddRegistered("VIEW_PLAYER") end
				if presentClasses["Players"] then
					context:AddRegistered("SELECT_LOCAL_PLAYER")
					context:AddRegistered("SELECT_ALL_CHARACTERS")
				end

				if presentClasses["LuaSourceContainer"] then
					context:AddRegistered("VIEW_SCRIPT", not presentClasses.isViableDecompileScript or env.decompile == nil)
					context:AddRegistered("SAVE_SCRIPT", not presentClasses.isViableDecompileScript or env.decompile == nil or env.writefile == nil)
					context:AddRegistered("SAVE_BYTECODE", not presentClasses.isViableDecompileScript or env.getscriptbytecode == nil or env.writefile == nil)
				end

				if sMap[nilNode] then
					context:AddRegistered("REFRESH_NIL")
					context:AddRegistered("HIDE_NIL")
				end

				Explorer.LastRightClickX, Explorer.LastRightClickY = Mouse.X, Mouse.Y
				context:Show(Mouse.X, Mouse.Y)
			end

			Explorer.InitRightClick = function()
				local context = Lib.ContextMenu.new()

				context:Register("CUT",{Name = "剪切", IconMap = Explorer.MiscIcons, Icon = "Cut", DisabledIcon = "Cut_Disabled", Shortcut = "Ctrl+Z", OnClick = function()
					local destroy,clone = game.Destroy,game.Clone
					local sList,newClipboard = selection.List,{}
					local count = 1
					for i = 1,#sList do
						local inst = sList[i].Obj
						local s,cloned = pcall(clone,inst)
						if s and cloned then
							newClipboard[count] = cloned
							count = count + 1
						end
						pcall(destroy,inst)
					end
					clipboard = newClipboard
					selection:Clear()
				end})

				context:Register("COPY",{Name = "复制", IconMap = Explorer.MiscIcons, Icon = "Copy", DisabledIcon = "Copy_Disabled", Shortcut = "Ctrl+C", OnClick = function()
					local clone = game.Clone
					local sList,newClipboard = selection.List,{}
					local count = 1
					for i = 1,#sList do
						local inst = sList[i].Obj
						local s,cloned = pcall(clone,inst)
						if s and cloned then
							newClipboard[count] = cloned
							count = count + 1
						end
					end
					clipboard = newClipboard
				end})

				context:Register("PASTE",{Name = "粘贴到", IconMap = Explorer.MiscIcons, Icon = "Paste", DisabledIcon = "Paste_Disabled", Shortcut = "Ctrl+Shift+V", OnClick = function()
					local sList = selection.List
					local newSelection = {}
					local count = 1
					for i = 1,#sList do
						local node = sList[i]
						local inst = node.Obj
						Explorer.MakeNodeVisible(node,true)
						for c = 1,#clipboard do
							local cloned = clipboard[c]:Clone()
							if cloned then
								cloned.Parent = inst
								local clonedNode = nodes[cloned]
								if clonedNode then newSelection[count] = clonedNode count = count + 1 end
							end
						end
					end
					selection:SetTable(newSelection)

					if #newSelection > 0 then
						Explorer.ViewNode(newSelection[1])
					end
				end})

				context:Register("DUPLICATE",{Name = "复制", IconMap = Explorer.MiscIcons, Icon = "Copy", DisabledIcon = "Copy_Disabled", Shortcut = "Ctrl+D", OnClick = function()
					local clone = game.Clone
					local sList = selection.List
					local newSelection = {}
					local count = 1
					for i = 1,#sList do
						local node = sList[i]
						local inst = node.Obj
						local instPar = node.Parent and node.Parent.Obj
						Explorer.MakeNodeVisible(node)
						local s,cloned = pcall(clone,inst)
						if s and cloned then
							cloned.Parent = instPar
							local clonedNode = nodes[cloned]
							if clonedNode then newSelection[count] = clonedNode count = count + 1 end
						end
					end

					selection:SetTable(newSelection)
					if #newSelection > 0 then
						Explorer.ViewNode(newSelection[1])
					end
				end})

				context:Register("DELETE",{Name = "删除", IconMap = Explorer.MiscIcons, Icon = "Delete", DisabledIcon = "Delete_Disabled", Shortcut = "Del", OnClick = function()
					local destroy = game.Destroy
					local sList = selection.List
					for i = 1,#sList do
						pcall(destroy,sList[i].Obj)
					end
					selection:Clear()
				end})

				context:Register("RENAME",{Name = "重命名", IconMap = Explorer.MiscIcons, Icon = "Rename", DisabledIcon = "Rename_Disabled", Shortcut = "F2", OnClick = function()
					local sList = selection.List
					if sList[1] then
						Explorer.SetRenamingNode(sList[1])
					end
				end})

				context:Register("GROUP",{Name = "组合", IconMap = Explorer.MiscIcons, Icon = "Group", DisabledIcon = "Group_Disabled", Shortcut = "Ctrl+G", OnClick = function()
					local sList = selection.List
					if #sList == 0 then return end

					local model = Instance.new("Model",sList[#sList].Obj.Parent)
					for i = 1,#sList do
						pcall(function() sList[i].Obj.Parent = model end)
					end

					if nodes[model] then
						selection:Set(nodes[model])
						Explorer.ViewNode(nodes[model])
					end
				end})

				context:Register("UNGROUP",{Name = "解组", IconMap = Explorer.MiscIcons, Icon = "Ungroup", DisabledIcon = "Ungroup_Disabled", Shortcut = "Ctrl+U", OnClick = function()
					local newSelection = {}
					local count = 1
					local isa = game.IsA

					local function ungroup(node)
						local par = node.Parent.Obj
						local ch = {}
						local chCount = 1

						for i = 1,#node do
							local n = node[i]
							newSelection[count] = n
							ch[chCount] = n
							count = count + 1
							chCount = chCount + 1
						end

						for i = 1,#ch do
							pcall(function() ch[i].Obj.Parent = par end)
						end

						node.Obj:Destroy()
					end

					for i,v in next,selection.List do
						if isa(v.Obj,"Model") then
							ungroup(v)
						end
					end

					selection:SetTable(newSelection)
					if #newSelection > 0 then
						Explorer.ViewNode(newSelection[1])
					end
				end})

				context:Register("SELECT_CHILDREN",{Name = "选择子项", IconMap = Explorer.MiscIcons, Icon = "SelectChildren", DisabledIcon = "SelectChildren_Disabled", OnClick = function()
					local newSelection = {}
					local count = 1
					local sList = selection.List

					for i = 1,#sList do
						local node = sList[i]
						for ind = 1,#node do
							local cNode = node[ind]
							if ind == 1 then Explorer.MakeNodeVisible(cNode) end

							newSelection[count] = cNode
							count = count + 1
						end
					endselection:SetTable(newSelection)
					if #newSelection > 0 then
						Explorer.ViewNode(newSelection[1])
					else
						Explorer.Refresh()
					end
				end})

				context:Register("JUMP_TO_PARENT",{Name = "跳转到父项", IconMap = Explorer.MiscIcons, Icon = "JumpToParent", OnClick = function()
					local newSelection = {}
					local count = 1
					local sList = selection.List

					for i = 1,#sList do
						local node = sList[i]
						if node.Parent then
							newSelection[count] = node.Parent
							count = count + 1
						end
					end

					selection:SetTable(newSelection)
					if #newSelection > 0 then
						Explorer.ViewNode(newSelection[1])
					else
						Explorer.Refresh()
					end
				end})

				context:Register("TELEPORT_TO",{Name = "传送到", IconMap = Explorer.MiscIcons, Icon = "TeleportTo", OnClick = function()
					local sList = selection.List
					local plrRP = plr.Character and plr.Character:FindFirstChild("HumanoidRootPart")

					if not plrRP then return end

					for _,node in next, sList do
						local Obj = node.Obj

						if Obj:IsA("BasePart") then
							if Obj.CanCollide then
								plr.Character:MoveTo(Obj.Position)
							else
								plrRP.CFrame = CFrame.new(Obj.Position + Settings.Explorer.TeleportToOffset)
							end
							break
						elseif Obj:IsA("Model") then
							if Obj.PrimaryPart then
								if Obj.PrimaryPart.CanCollide then
									plr.Character:MoveTo(Obj.PrimaryPart.Position)
								else
									plrRP.CFrame = CFrame.new(Obj.PrimaryPart.Position + Settings.Explorer.TeleportToOffset)
								end
								break
							else
								local part = Obj:FindFirstChildWhichIsA("BasePart", true)
								if part and nodes[part] then
									if part.CanCollide then
										plr.Character:MoveTo(part.Position)
									else
										plrRP.CFrame = CFrame.new(part.Position + Settings.Explorer.TeleportToOffset)
									end
									break
								elseif Obj.WorldPivot then
									plrRP.CFrame = Obj.WorldPivot
								end
							end
						end
					end
				end})

				local OldAnimation
				context:Register("PLAY_TWEEN",{Name = "播放动画", IconMap = Explorer.MiscIcons, Icon = "Play", OnClick = function()
					local sList = selection.List

					for i = 1, #sList do
						local node = sList[i]
						local Obj = node.Obj

						if Obj:IsA("Tween") then Obj:Play() end
					end
				end})

				local OldAnimation
				context:Register("LOAD_ANIMATION",{Name = "加载动画", IconMap = Explorer.MiscIcons, Icon = "Play", OnClick = function()
					local sList = selection.List

					local Humanoid = plr.Character and plr.Character:FindFirstChild("Humanoid")
					if not Humanoid then return end

					for i = 1, #sList do
						local node = sList[i]
						local Obj = node.Obj

						if Obj:IsA("Animation") then
							if OldAnimation then OldAnimation:Stop() end
							OldAnimation = Humanoid:LoadAnimation(Obj)
							OldAnimation:Play()
							break
						end
					end
				end})

				context:Register("STOP_ANIMATION",{Name = "停止动画", IconMap = Explorer.MiscIcons, Icon = "Pause", OnClick = function()
					local sList = selection.List

					local Humanoid = plr.Character and plr.Character:FindFirstChild("Humanoid")
					if not Humanoid then return end

					for i = 1, #sList do
						local node = sList[i]
						local Obj = node.Obj

						if Obj:IsA("Animation") then
							if OldAnimation then OldAnimation:Stop() end
							Humanoid:LoadAnimation(Obj):Stop()
							break
						end
					end
				end})

				context:Register("EXPAND_ALL",{Name = "全部展开", OnClick = function()
					local sList = selection.List

					local function expand(node)
						expanded[node] = true
						for i = 1,#node do
							if #node[i] > 0 then
								expand(node[i])
							end
						end
					end

					for i = 1,#sList do
						expand(sList[i])
					end

					Explorer.ForceUpdate()
				end})

				context:Register("COLLAPSE_ALL",{Name = "全部折叠", OnClick = function()
					local sList = selection.List

					local function expand(node)
						expanded[node] = nil
						for i = 1,#node do
							if #node[i] > 0 then
								expand(node[i])
							end
						end
					end

					for i = 1,#sList do
						expand(sList[i])
					end

					Explorer.ForceUpdate()
				end})

				context:Register("CLEAR_SEARCH_AND_JUMP_TO",{Name = "清除搜索并跳转到", OnClick = function()
					local newSelection = {}
					local count = 1
					local sList = selection.List

					for i = 1,#sList do
						newSelection[count] = sList[i]
						count = count + 1
					end

					selection:SetTable(newSelection)
					Explorer.ClearSearch()
					if #newSelection > 0 then
						Explorer.ViewNode(newSelection[1])
					end
				end})

				-- this code is very bad but im lazy and it works so cope
				local clth = function(str)
					if str:sub(1, 28) == "game:GetService(\"Workspace\")" then str = str:gsub("game:GetService%(\"Workspace\"%)", "workspace", 1) end
					if str:sub(1, 27 + #plr.Name) == "game:GetService(\"Players\")." .. plr.Name then str = str:gsub("game:GetService%(\"Players\"%)." .. plr.Name, "game:GetService(\"Players\").LocalPlayer", 1) end
					return str
				end

				context:Register("COPY_PATH",{Name = "复制路径", IconMap = Explorer.ClassIcons, Icon = 50, OnClick = function()
					local sList = selection.List
					if #sList == 1 then
						env.setclipboard(clth(Explorer.GetInstancePath(sList[1].Obj)))
					elseif #sList > 1 then
						local resList = {"{"}
						local count = 2
						for i = 1,#sList do
							local path = "\t"..clth(Explorer.GetInstancePath(sList[i].Obj))..","
							if #path > 0 then
								resList[count] = path
								count = count+1
							end
						end
						resList[count] = "}"
						env.setclipboard(table.concat(resList,"\n"))
					end
				end})

				context:Register("INSERT_OBJECT",{Name = "插入对象", IconMap = Explorer.MiscIcons, Icon = "InsertObject", OnClick = function()
					local mouse = Main.Mouse
					local x,y = Explorer.LastRightClickX or mouse.X, Explorer.LastRightClickY or mouse.Y
					Explorer.InsertObjectContext:Show(x,y)
				end})

				--[[context:Register("CALL_FUNCTION",{Name = "Call Function", IconMap = Explorer.ClassIcons, Icon = 66, OnClick = function()

				end})

				context:Register("GET_REFERENCES",{Name = "Get Lua References", IconMap = Explorer.ClassIcons, Icon = 34, OnClick = function()

				end})

				context:Register("SAVE_INST",{Name = "Save to File", IconMap = Explorer.MiscIcons, Icon = "Save", OnClick = function()

				end})

                context:Register("VIEW_CONNECTIONS",{Name = "View Connections", OnClick = function()
                    
                end})

				context:Register("VIEW_API",{Name = "View API Page", IconMap = Explorer.MiscIcons, Icon = "Reference", OnClick = function()

				end})]]

				context:Register("VIEW_OBJECT",{Name = "查看对象 (右键重置)", IconMap = Explorer.ClassIcons, Icon = 5, OnClick = function()
					local sList = selection.List
					local isa = game.IsA

					for i = 1,#sList do
						local node = sList[i]

						if isa(node.Obj,"BasePart") or isa(node.Obj, "Model") then
							workspace.CurrentCamera.CameraSubject = node.Obj
							break
						end
					end
				end, OnRightClick = function()
					workspace.CurrentCamera.CameraSubject = plr.Character
				end})

				context:Register("FIRE_TOUCHTRANSMITTER",{Name = "触发触摸发射器", IconMap = Explorer.ClassIcons, Icon = 37, OnClick = function()
					local hrp = plr.Character and plr.Character:FindFirstChild("HumanoidRootPart")
					if not hrp then return end
					for _, v in ipairs(selection.List) do if v.Obj and v.Obj:IsA("TouchTransmitter") then firetouchinterest(hrp, v.Obj.Parent, 0) end end
				end})

				context:Register("FIRE_CLICKDETECTOR",{Name = "触发点击检测器", IconMap = Explorer.ClassIcons, Icon = 41, OnClick = function()
					local hrp = plr.Character and plr.Character:FindFirstChild("HumanoidRootPart")
					if not hrp then return end
					for _, v in ipairs(selection.List) do if v.Obj and v.Obj:IsA("ClickDetector") then fireclickdetector(v.Obj) end end
				end})

				context:Register("FIRE_PROXIMITYPROMPT",{Name = "触发接近提示", IconMap = Explorer.ClassIcons, Icon = 124, OnClick = function()
					local hrp = plr.Character and plr.Character:FindFirstChild("HumanoidRootPart")
					if not hrp then return end
					for _, v in ipairs(selection.List) do if v.Obj and v.Obj:IsA("ProximityPrompt") then fireproximityprompt(v.Obj) end end
				end})

				context:Register("VIEW_SCRIPT",{Name = "查看脚本", IconMap = Explorer.MiscIcons, Icon = "ViewScript", OnClick = function()
					local scr = selection.List[1] and selection.List[1].Obj
					if scr then ScriptViewer.ViewScript(scr) end
				end})

				context:Register("SAVE_SCRIPT",{Name = "保存脚本", IconMap = Explorer.MiscIcons, Icon = "Save", OnClick = function()
					for _, v in next, selection.List do
						if v.Obj:IsA("LuaSourceContainer") and env.isViableDecompileScript(v.Obj) then
							local success, source = pcall(env.decompile, v.Obj)
							if not success or not source then source = ("-- DEX - %s failed to decompile %s"):format(env.executor, v.Obj.ClassName) end
							local fileName = ("%i.%s.%s.Source.txt"):format(game.PlaceId, v.Obj.ClassName, env.parsefile(v.Obj.Name))
							env.writefile(fileName, source)
							task.wait(0.2)
						end
					end
				end})

				context:Register("SAVE_BYTECODE",{Name = "保存脚本字节码", IconMap = Explorer.MiscIcons, Icon = "Save", OnClick = function()
					for _, v in next, selection.List do
						if v.Obj:IsA("LuaSourceContainer") and env.isViableDecompileScript(v.Obj) then
							local success, bytecode = pcall(getscriptbytecode, v.Obj)
							if success and type(bytecode) == "string" then
								local fileName = ("%i.%s.%s.Bytecode.txt"):format(game.PlaceId, v.Obj.ClassName, env.parsefile(v.Obj.Name))
								env.writefile(fileName, bytecode)
								task.wait(0.2)
							end
						end
					end
				end})

				context:Register("SELECT_CHARACTER",{Name = "选择角色", IconMap = Explorer.ClassIcons, Icon = 9, OnClick = function()
					local newSelection = {}
					local count = 1
					local sList = selection.List
					local isa = game.IsA

					for i = 1,#sList do
						local node = sList[i]
						if isa(node.Obj,"Player") and nodes[node.Obj.Character] then
							newSelection[count] = nodes[node.Obj.Character]
							count = count + 1
						end
					end

					selection:SetTable(newSelection)
					if #newSelection > 0 then
						Explorer.ViewNode(newSelection[1])
					else
						Explorer.Refresh()
					end
				end})

				context:Register("VIEW_PLAYER",{Name = "查看玩家", IconMap = Explorer.ClassIcons, Icon = 5, OnClick = function()
					local newSelection = {}
					local count = 1
					local sList = selection.List
					local isa = game.IsA

					for i = 1,#sList do
						local node = sList[i]
						local Obj = node.Obj
						if Obj:IsA("Player") and Obj.Character then
							workspace.CurrentCamera.CameraSubject = Obj.Character
							break
						end
					end
				end})

				context:Register("SELECT_LOCAL_PLAYER",{Name = "选择本地玩家", IconMap = Explorer.ClassIcons, Icon = 9, OnClick = function()
					pcall(function() if nodes[plr] then selection:Set(nodes[plr]) Explorer.ViewNode(nodes[plr]) end end)
				end})

				context:Register("SELECT_ALL_CHARACTERS",{Name = "选择所有角色", IconMap = Explorer.ClassIcons, Icon = 2, OnClick = function()
					local newSelection = {}
					local sList = selection.List

					for i,v in next, service.Players:GetPlayers() do
						if v.Character and nodes[v.Character] then
							if i == 1 then Explorer.MakeNodeVisible(v.Character) end
							table.insert(newSelection, nodes[v.Character])
						end
					end

					selection:SetTable(newSelection)
					if #newSelection > 0 then
						Explorer.ViewNode(newSelection[1])
					else
						Explorer.Refresh()
					end
				end})

				context:Register("REFRESH_NIL",{Name = "刷新无效实例", OnClick = function()
					Explorer.RefreshNilInstances()
				end})

				context:Register("HIDE_NIL",{Name = "隐藏无效实例", OnClick = function()
					Explorer.HideNilInstances()
				end})

				Explorer.RightClickContext = context
			end

			Explorer.HideNilInstances = function()
				table.clear(nilMap)

				local disconnectCon = Instance.new("Folder").ChildAdded:Connect(function() end).Disconnect
				for i,v in next,nilCons do
					disconnectCon(v[1])
					disconnectCon(v[2])
				end
				table.clear(nilCons)

				for i = 1,#nilNode do
					coroutine.wrap(removeObject)(nilNode[i].Obj)
				end

				Explorer.Update()
				Explorer.Refresh()
			end

			Explorer.RefreshNilInstances = function()
				if not env.getnilinstances then return end

				local nilInsts = env.getnilinstances()
				local game = game
				local getDescs = game.GetDescendants
				--local newNilMap = {}
				--local newNilRoots = {}
				--local nilRoots = Explorer.NilRoots
				--local connect = game.DescendantAdded.Connect
				--local disconnect
				--if not nilRoots then nilRoots = {} Explorer.NilRoots = nilRoots end

				for i = 1,#nilInsts do
					local obj = nilInsts[i]
					if obj ~= game then
						nilMap[obj] = true
						--newNilRoots[obj] = true

						local descs = getDescs(obj)
						for j = 1,#descs do
							nilMap[descs[j]] = true
						end
					end
				end

				-- Remove unmapped nil nodes
		--[[for i = 1,#nilNode do
			local node = nilNode[i]
			if not newNilMap[node.Obj] then
				nilMap[node.Obj] = nil
				coroutine.wrap(removeObject)(node)
			end
		end]]

				--nilMap = newNilMap

				for i = 1,#nilInsts do
					local obj = nilInsts[i]
					local node = nodes[obj]
					if not node then coroutine.wrap(addObject)(obj) end
				end

		--[[
		-- Remove old root connections
		for obj in next,nilRoots do
			if not newNilRoots[obj] then
				if not disconnect then disconnect = obj[1].Disconnect end
				disconnect(obj[1])
				disconnect(obj[2])
			end
		end
		
		for obj in next,newNilRoots do
			if not nilRoots[obj] then
				nilRoots[obj] = {
					connect(obj.DescendantAdded,addObject),
					connect(obj.DescendantRemoving,removeObject)
				}
			end
		end]]

				--nilMap = newNilMap
				--Explorer.NilRoots = newNilRoots

				Explorer.Update()
				Explorer.Refresh()
			end

			Explorer.GetInstancePath = function(obj)
				local ffc = game.FindFirstChild
				local getCh = game.GetChildren
				local path = ""
				local curObj = obj
				local ts = tostring
				local match = string.match
				local gsub = string.gsub
				local tableFind = table.find
				local useGetCh = Settings.Explorer.CopyPathUseGetChildren
				local formatLuaString = Lib.FormatLuaString

				while curObj do
					if curObj == game then
						path = "game"..path
						break
					end

					local className = curObj.ClassName
					local curName = ts(curObj)
					local indexName
					if match(curName,"^[%a_][%w_]*$") then
						indexName = "."..curName
					else
						local cleanName = formatLuaString(curName)
						indexName = '["'..cleanName..'"]'
					end

					local parObj = curObj.Parent
					if parObj then
						local fc = ffc(parObj,curName)
						if useGetCh and fc and fc ~= curObj then
							local parCh = getCh(parObj)
							local fcInd = tableFind(parCh,curObj)
							indexName = ":GetChildren()["..fcInd.."]"
						elseif parObj == game and API.Classes[className] and API.Classes[className].Tags.Service then
							indexName = ':GetService("'..className..'")'
						end
					elseif parObj == nil then
						local getnil = "local getNil = function(name, class) for _, v in next, getnilinstances() do if v.ClassName == class and v.Name == name then return v end end end"
						local gotnil = "\n\ngetNil(\"%s\", \"%s\")"
						indexName = getnil .. gotnil:format(curObj.Name, className)
					end

					path = indexName..path
					curObj = parObj
				end

				return path
			end

			Explorer.DefaultProps = {
				["BasePart"] = {
					Position = function(Obj)
						local Player = service.Players.LocalPlayer
						if Player.Character and Player.Character:FindFirstChild("HumanoidRootPart") then
							Obj.Position = (Player.Character.HumanoidRootPart.CFrame * CFrame.new(0, 0, -10)).p
						end
						return Obj.Position
					end,
					Anchored = true
				},
				["GuiObject"] = {
					Position = function(Obj) return (Obj.Parent:IsA("ScreenGui") and UDim2.new(0.5, 0, 0.5, 0)) or Obj.Position end,
					Active = true
				}
			}

			Explorer.InitInsertObject = function()
				local context = Lib.ContextMenu.new()
				context.SearchEnabled = true
				context.MaxHeight = 400
				context:ApplyTheme({
					ContentColor = Settings.Theme.Main2,
					OutlineColor = Settings.Theme.Outline1,
					DividerColor = Settings.Theme.Outline1,
					TextColor = Settings.Theme.Text,
					HighlightColor = Settings.Theme.ButtonHover
				})

				local classes = {}
				for i,class in next,API.Classes do
					local tags = class.Tags
					if not tags.NotCreatable and not tags.Service then
						local rmdEntry = RMD.Classes[class.Name]
						classes[#classes+1] = {class,rmdEntry and rmdEntry.ClassCategory or "Uncategorized"}
					end
				end
				table.sort(classes,function(a,b)
					if a[2] ~= b[2] then
						return a[2] < b[2]
					else
						return a[1].Name < b[1].Name
					end
				end)

				local function defaultProps(obj)
					for class, props in pairs(Explorer.DefaultProps) do
						if obj:IsA(class) then
							for prop, value in pairs(props) do
								obj[prop] = (type(value) == "function" and value(obj)) or value
							end
						end
					end
				endlocal function onClick(className)
					local sList = selection.List
					local instNew = Instance.new
					for i = 1,#sList do
						local node = sList[i]
						local obj = node.Obj
						Explorer.MakeNodeVisible(node, true)
						local success, obj = pcall(instNew, className, obj)
						if success and obj then defaultProps(obj) end
					end
				end

				local lastCategory = ""
				for i = 1,#classes do
					local class = classes[i][1]
					local rmdEntry = RMD.Classes[class.Name]
					local iconInd = rmdEntry and tonumber(rmdEntry.ExplorerImageIndex) or 0
					local category = classes[i][2]

					if lastCategory ~= category then
						context:AddDivider(category)
						lastCategory = category
					end
					context:Add({Name = class.Name, IconMap = Explorer.ClassIcons, Icon = iconInd, OnClick = onClick})
				end

				Explorer.InsertObjectContext = context
			end

			Explorer._SearchFilters = {} do
				local Filters = Explorer._SearchFilters

				local function NewFilter(list, func)
					for _,v in next, list do
						Filters[v:lower() .. ":"] = func
					end
				end

				local Only = {
					remotes = {"RemoteEvent", "RemoteFunction", "BindableEvent", "BindableFunction"},
					scripts = {"Script", "LocalScript", "ModuleScript"},
					players = {"Player"}
				}

				NewFilter({"parent", "p"}, function(Obj, str) return Obj.Parent and (Obj.Parent.Name:lower()):find(str) end)
				NewFilter({"class", "c"}, function(Obj, str) return (Obj.ClassName:lower()):find(str) end)
				NewFilter({"isa", "i"}, function(Obj, str) return Obj:IsA(str) end)

				NewFilter({"only", "o"}, function(Obj, str)
					local Special = Only[str]
					return Special and table.find(Special, Obj.ClassName)
				end)
			end

			Explorer.DoSearch = function(query)
				table.clear(Explorer.SearchExpanded)
				table.clear(searchResults)
				expanded = (#query == 0 and Explorer.Expanded) or Explorer.SearchExpanded

				local tostr = tostring;
				local tfind = table.find;

				local Filters = Explorer._SearchFilters
				local expandTable = Explorer.SearchExpanded

				local allnodes = nodes[game]

				local defaultSearch = (function(Obj, str) return (Obj.Name:lower()):find(str, 1, true) end)

				local function searchTable(root, str, func)
					local expandedpar = false
					for _,node in ipairs(root) do
						if func(node.Obj, str) then
							expandTable[node] = 0
							searchResults[node] = true
							if not expandedpar then
								local parnode = node.Parent
								while parnode and (not searchResults[parnode] or expandTable[parnode] == 0) do
									expanded[parnode] = true
									searchResults[parnode] = true
									parnode = parnode.Parent
								end
								expandedpar = true
							end
						end

						if #node > 0 then searchTable(node, str, func) end
					end
				end

				local function Search(query)
					if query:len() == 0 then return end

					local lower = query:lower()
					local split = lower:split(":")
					local Filter = (Filters[split[1] .. ":"]) or nil

					if Filter then
						searchTable(allnodes, (split[2] or ""), Filter)
					else
						searchTable(allnodes, (lower or ""), defaultSearch)
					end
				end

				for _,v in ipairs(query:split(",")) do
					if v:len() > 0 then
						Search(v)
					end
				end

		--[=[if #query > 0 then
			local expandTable = Explorer.SearchExpanded
			local specFilters
			
			local lower = string.lower
			local find = string.find
			local tostring = tostring
			
			local lowerQuery = lower(query)
			
			local function defaultSearch(root)
				local expandedpar = false
				for i = 1,#root do
					local node = root[i]
					local obj = node.Obj
					
					if find(lower(tostring(obj)),lowerQuery,1,true) then
						expandTable[node] = 0
						searchResults[node] = true
						if not expandedpar then
							local parnode = node.Parent
							while parnode and (not searchResults[parnode] or expandTable[parnode] == 0) do
								expanded[parnode] = true
								searchResults[parnode] = true
								parnode = parnode.Parent
							end
							expandedpar = true
						end
					elseif ExplorerSearch[lower(tostring(obj))] then
						
					end
					
					if #node > 0 then defaultSearch(node) end
				end
			end

			if Main.Elevated then
				local start = tick()
				searchFunc,specFilters = Explorer.BuildSearchFunc(query)
				--print("BUILD SEARCH",tick()-start)
			else
				searchFunc = defaultSearch
			end

			if specFilters then
				table.clear(specResults)
				for i = 1,#specFilters do -- Specific search filers that returns list of matches
					local resMap = {}
					specResults[i] = resMap
					local objs = specFilters[i]()
					for c = 1,#objs do
						local node = nodes[objs[c]]
						if node then
							resMap[node] = true
						end
					end
				end
			end
			
			if searchFunc then
				local start = tick()
				searchFunc(nodes[game])
				searchFunc(nilNode)
				--warn(tick()-start)
			end
		end]=]

				Explorer.ForceUpdate()
			end

			Explorer.ClearSearch = function()
				Explorer.GuiElems.SearchBar.Text = ""
				expanded = Explorer.Expanded
				searchFunc = nil
			end

			Explorer.InitSearch = function()
				local TweenService = service.TweenService
				local SearchFrame = Explorer.GuiElems.ToolBar.SearchFrame
				local searchBox = SearchFrame.SearchBox
				Explorer.GuiElems.SearchBar = searchBox

				local TweenInfo = TweenInfo.new(0.2, Enum.EasingStyle.Quint)
				local Tweens = {
					Start = TweenService:Create(SearchFrame.UIStroke, TweenInfo, { Color = Color3.fromRGB(0, 120, 215) }),
					End = TweenService:Create(SearchFrame.UIStroke, TweenInfo, { Color = Color3.fromRGB(42, 42, 42) })
				}

				searchBox.FocusLost:Connect(function() Tweens.End:Play() end)
				searchBox.Focused:Connect(function() Tweens.Start:Play() end)

				Lib.ViewportTextBox.convert(searchBox)

				searchBox.FocusLost:Connect(function()
					Explorer.DoSearch(searchBox.Text)
				end)
			end

			Explorer.InitEntryTemplate = function()
				entryTemplate = create({
					{1,"TextButton",{AutoButtonColor=false,BackgroundColor3=Color3.new(0,0,0),BackgroundTransparency=1,BorderColor3=Color3.new(0,0,0),Font=3,Name="Entry",Position=UDim2.new(0,1,0,1),Size=UDim2.new(0,250,0,20),Text="",TextSize=14,}},
					{2,"Frame",{BackgroundColor3=Color3.new(0.04313725605607,0.35294118523598,0.68627452850342),BackgroundTransparency=1,BorderColor3=Color3.new(0.33725491166115,0.49019610881805,0.73725491762161),BorderSizePixel=0,Name="Indent",Parent={1},Position=UDim2.new(0,20,0,0),Size=UDim2.new(1,-20,1,0),}},
					{3,"TextLabel",{BackgroundColor3=Color3.new(1,1,1),BackgroundTransparency=1,Font=3,Name="EntryName",Parent={2},Position=UDim2.new(0,26,0,0),Size=UDim2.new(1,-26,1,0),Text="Workspace",TextColor3=Color3.new(0.86274516582489,0.86274516582489,0.86274516582489),TextSize=14,TextXAlignment=0,}},
					{4,"TextButton",{BackgroundColor3=Color3.new(1,1,1),BackgroundTransparency=1,ClipsDescendants=true,Font=3,Name="Expand",Parent={2},Position=UDim2.new(0,-20,0,0),Size=UDim2.new(0,20,0,20),Text="",TextSize=14,}},
					{5,"ImageLabel",{BackgroundColor3=Color3.new(1,1,1),BackgroundTransparency=1,Image="rbxassetid://5642383285",ImageRectOffset=Vector2.new(144,16),ImageRectSize=Vector2.new(16,16),Name="Icon",Parent={4},Position=UDim2.new(0,2,0,2),ScaleType=4,Size=UDim2.new(0,16,0,16),}},
					{6,"ImageLabel",{BackgroundColor3=Color3.new(1,1,1),BackgroundTransparency=1,ImageRectOffset=Vector2.new(304,0),ImageRectSize=Vector2.new(16,16),Name="Icon",Parent={2},Position=UDim2.new(0,4,0,2),ScaleType=4,Size=UDim2.new(0,16,0,16),}},
				})

				local sys = Lib.ClickSystem.new()
				sys.AllowedButtons = {1,2}
				sys.OnDown:Connect(function(item,combo,button)
					local ind = table.find(listEntries,item)
					if not ind then return end
					local node = tree[ind + Explorer.Index]
					if not node then return end

					local entry = listEntries[ind]

					if button == 1 then
						if combo == 2 then
							if node.Obj:IsA("LuaSourceContainer") then
								ScriptViewer.ViewScript(node.Obj)
							elseif #node > 0 and expanded[node] ~= 0 then
								expanded[node] = not expanded[node]
								Explorer.Update()
							end
						end

						if Properties.SelectObject(node.Obj) then
							sys.IsRenaming = false
							return
						end

						sys.IsRenaming = selection.Map[node]

						if Lib.IsShiftDown() then
							if not selection.Piviot then return end

							local fromIndex = table.find(tree,selection.Piviot)
							local toIndex = table.find(tree,node)
							if not fromIndex or not toIndex then return end
							fromIndex,toIndex = math.min(fromIndex,toIndex),math.max(fromIndex,toIndex)

							local sList = selection.List
							for i = #sList,1,-1 do
								local elem = sList[i]
								if selection.ShiftSet[elem] then
									selection.Map[elem] = nil
									table.remove(sList,i)
								end
							end
							selection.ShiftSet = {}
							for i = fromIndex,toIndex do
								local elem = tree[i]
								if not selection.Map[elem] then
									selection.ShiftSet[elem] = true
									selection.Map[elem] = true
									sList[#sList+1] = elem
								end
							end
							selection.Changed:Fire()
						elseif Lib.IsCtrlDown() then
							selection.ShiftSet = {}
							if selection.Map[node] then selection:Remove(node) else selection:Add(node) end
							selection.Piviot = node
							sys.IsRenaming = false
						elseif not selection.Map[node] then
							selection.ShiftSet = {}
							selection:Set(node)
							selection.Piviot = node
						end
					elseif button == 2 then
						if Properties.SelectObject(node.Obj) then
							return
						end

						if not Lib.IsCtrlDown() and not selection.Map[node] then
							selection.ShiftSet = {}
							selection:Set(node)
							selection.Piviot = node
							Explorer.Refresh()
						end
					end

					Explorer.Refresh()
				end)

				sys.OnRelease:Connect(function(item,combo,button,position)
					local ind = table.find(listEntries,item)
					if not ind then return end
					local node = tree[ind + Explorer.Index]
					if not node then return end

					if button == 1 then
						if selection.Map[node] and not Lib.IsShiftDown() and not Lib.IsCtrlDown() then
							selection.ShiftSet = {}
							selection:Set(node)
							selection.Piviot = node
							Explorer.Refresh()
						end

						local id = sys.ClickId
						Lib.FastWait(sys.ComboTime)
						if combo == 1 and id == sys.ClickId and sys.IsRenaming and selection.Map[node] then
							Explorer.SetRenamingNode(node)
						end
					elseif button == 2 then
						Explorer.ShowRightClick(position)
					end
				end)
				Explorer.ClickSystem = sys
			end

			Explorer.InitDelCleaner = function()
				coroutine.wrap(function()
					local fw = Lib.FastWait
					while true do
						local processed = false
						local c = 0
						for _,node in next,nodes do
							if node.HasDel then
								local delInd
								for i = 1,#node do
									if node[i].Del then
										delInd = i
										break
									end
								end
								if delInd then
									for i = delInd+1,#node do
										local cn = node[i]
										if not cn.Del then
											node[delInd] = cn
											delInd = delInd+1
										end
									end
									for i = delInd,#node do
										node[i] = nil
									end
								end
								node.HasDel = false
								processed = true
								fw()
							end
							c = c + 1
							if c > 10000 then
								c = 0
								fw()
							end
						end
						if processed and not refreshDebounce then Explorer.PerformRefresh() end
						fw(0.5)
					end
				end)()
			end

			Explorer.UpdateSelectionVisuals = function()
				local holder = Explorer.SelectionVisualsHolder
				local isa = game.IsA
				local clone = game.Clone
				if not holder then
					holder = Instance.new("ScreenGui")
					holder.Name = "ExplorerSelections"
					holder.DisplayOrder = Main.DisplayOrders.Core
					Lib.ShowGui(holder)
					Explorer.SelectionVisualsHolder = holder
					Explorer.SelectionVisualCons = {}

					local guiTemplate = create({
						{1,"Frame",{BackgroundColor3=Color3.new(1,1,1),BackgroundTransparency=1,Size=UDim2.new(0,100,0,100),}},
						{2,"Frame",{BackgroundColor3=Color3.new(0.04313725605607,0.35294118523598,0.68627452850342),BorderSizePixel=0,Parent={1},Position=UDim2.new(0,-1,0,-1),Size=UDim2.new(1,2,0,1),}},
						{3,"Frame",{BackgroundColor3=Color3.new(0.04313725605607,0.35294118523598,0.68627452850342),BorderSizePixel=0,Parent={1},Position=UDim2.new(0,-1,1,0),Size=UDim2.new(1,2,0,1),}},
						{4,"Frame",{BackgroundColor3=Color3.new(0.04313725605607,0.35294118523598,0.68627452850342),BorderSizePixel=0,Parent={1},Position=UDim2.new(0,-1,0,0),Size=UDim2.new(0,1,1,0),}},
						{5,"Frame",{BackgroundColor3=Color3.new(0.04313725605607,0.35294118523598,0.68627452850342),BorderSizePixel=0,Parent={1},Position=UDim2.new(1,0,0,0),Size=UDim2.new(0,1,1,0),}},
					})
					Explorer.SelectionVisualGui = guiTemplate

					local boxTemplate = Instance.new("SelectionBox")
					boxTemplate.LineThickness = 0.03
					boxTemplate.Color3 = Color3.fromRGB(0, 170, 255)
					Explorer.SelectionVisualBox = boxTemplate
				end
				holder:ClearAllChildren()

				-- Updates theme
				for i,v in pairs(Explorer.SelectionVisualGui:GetChildren()) do
					v.BackgroundColor3 = Color3.fromRGB(0, 170, 255)
				end

				local attachCons = Explorer.SelectionVisualCons
				for i = 1,#attachCons do
					attachCons[i].Destroy()
				end
				table.clear(attachCons)

				local partEnabled = Settings.Explorer.PartSelectionBox
				local guiEnabled = Settings.Explorer.GuiSelectionBox
				if not partEnabled and not guiEnabled then return end

				local svg = Explorer.SelectionVisualGui
				local svb = Explorer.SelectionVisualBox
				local attachTo = Lib.AttachTo
				local sList = selection.List
				local count = 1
				local boxCount = 0
				local workspaceNode = nodes[workspace]
				for i = 1,#sList do
					if boxCount > 1000 then break end
					local node = sList[i]
					local obj = node.Obj

					if node ~= workspaceNode then
						if isa(obj,"GuiObject") and guiEnabled then
							local newVisual = clone(svg)
							attachCons[count] = attachTo(newVisual,{Target = obj, Resize = true})
							count = count + 1
							newVisual.Parent = holder
							boxCount = boxCount + 1
						elseif isa(obj,"PVInstance") and partEnabled then
							local newBox = clone(svb)
							newBox.Adornee = obj
							newBox.Parent = holder
							boxCount = boxCount + 1
						end
					end
				end
			end

			Explorer.Init = function()
				Explorer.ClassIcons = Lib.IconMap.newLinear("rbxasset://textures/ClassImages.PNG", 16, 16)
				Explorer.MiscIcons = Main.MiscIcons

				clipboard = {}

				selection = Lib.Set.new()
				selection.ShiftSet = {}
				selection.Changed:Connect(Properties.ShowExplorerProps)
				Explorer.Selection = selection

				Explorer.InitRightClick()
				Explorer.InitInsertObject()
				Explorer.SetSortingEnabled(Settings.Explorer.Sorting)
				Explorer.Expanded = setmetatable({},{__mode = "k"})
				Explorer.SearchExpanded = setmetatable({},{__mode = "k"})
				expanded = Explorer.Expanded

				nilNode.Obj.Name = "Nil Instances"
				nilNode.Locked = true

				local explorerItems = create({
					{1,"Folder",{Name="ExplorerItems",}},
					{2,"Frame",{BackgroundColor3=Color3.new(0.20392157137394,0.20392157137394,0.20392157137394),BorderSizePixel=0,Name="ToolBar",Parent={1},Size=UDim2.new(1,0,0,22),}},
					{3,"Frame",{BackgroundColor3=Color3.new(0.14901961386204,0.14901961386204,0.14901961386204),BorderColor3=Color3.new(0.1176470592618,0.1176470592618,0.1176470592618),BorderSizePixel=0,Name="SearchFrame",Parent={2},Position=UDim2.new(0,3,0,1),Size=UDim2.new(1,-6,0,18),}},
					{4,"TextBox",{BackgroundColor3=Color3.new(1,1,1),BackgroundTransparency=1,ClearTextOnFocus=false,Font=3,Name="SearchBox",Parent={3},PlaceholderColor3=Color3.new(0.39215689897537,0.39215689897537,0.39215689897537),PlaceholderText="搜索工作区",Position=UDim2.new(0,4,0,0),Size=UDim2.new(1,-24,0,18),Text="",TextColor3=Color3.new(1,1,1),TextSize=14,TextXAlignment=0,}},
					{5,"UICorner",{CornerRadius=UDim.new(0,2),Parent={3},}},
					{6,"UIStroke",{Thickness=1.4,Parent={3},Color=Color3.fromRGB(42,42,42)}},
					{7,"TextButton",{AutoButtonColor=false,BackgroundColor3=Color3.new(0.12549020349979,0.12549020349979,0.12549020349979),BackgroundTransparency=1,BorderSizePixel=0,Font=3,Name="Reset",Parent={3},Position=UDim2.new(1,-17,0,1),Size=UDim2.new(0,16,0,16),Text="",TextColor3=Color3.new(1,1,1),TextSize=14,}},
					{8,"ImageLabel",{BackgroundColor3=Color3.new(1,1,1),BackgroundTransparency=1,Image="rbxassetid://5034718129",ImageColor3=Color3.new(0.39215686917305,0.39215686917305,0.39215686917305),Parent={7},Size=UDim2.new(0,16,0,16),}},
					{9,"TextButton",{AutoButtonColor=false,BackgroundColor3=Color3.new(0.12549020349979,0.12549020349979,0.12549020349979),BackgroundTransparency=1,BorderSizePixel=0,Font=3,Name="Refresh",Parent={2},Position=UDim2.new(1,-20,0,1),Size=UDim2.new(0,18,0,18),Text="",TextColor3=Color3.new(1,1,1),TextSize=14,Visible=false,}},
					{10,"ImageLabel",{BackgroundColor3=Color3.new(1,1,1),BackgroundTransparency=1,Image="rbxassetid://5642310344",Parent={9},Position=UDim2.new(0,3,0,3),Size=UDim2.new(0,12,0,12),}},
					{11,"Frame",{BackgroundColor3=Color3.new(0.15686275064945,0.15686275064945,0.15686275064945),BorderSizePixel=0,Name="ScrollCorner",Parent={1},Position=UDim2.new(1,-16,1,-16),Size=UDim2.new(0,16,0,16),Visible=false,}},
					{12,"Frame",{BackgroundColor3=Color3.new(1,1,1),BackgroundTransparency=1,ClipsDescendants=true,Name="List",Parent={1},Position=UDim2.new(0,0,0,23),Size=UDim2.new(1,0,1,-23),}}
				})

				toolBar = explorerItems.ToolBar
				treeFrame = explorerItems.List

				Explorer.GuiElems.ToolBar = toolBar
				Explorer.GuiElems.TreeFrame = treeFrame

				scrollV = Lib.ScrollBar.new()		
				scrollV.WheelIncrement = 3
				scrollV.Gui.Position = UDim2.new(1,-16,0,23)
				scrollV:SetScrollFrame(treeFrame)
				scrollV.Scrolled:Connect(function()
					Explorer.Index = scrollV.Index
					Explorer.Refresh()
				end)

				scrollH = Lib.ScrollBar.new(true)
				scrollH.Increment = 5
				scrollH.WheelIncrement = Explorer.EntryIndent
				scrollH.Gui.Position = UDim2.new(0,0,1,-16)
				scrollH.Scrolled:Connect(function()
					Explorer.Refresh()
				end)

				local window = Lib.Window.new()
				Explorer.Window = window
				window:SetTitle("资源管理器")
				window.GuiElems.Line.Position = UDim2.new(0,0,0,22)

				Explorer.InitEntryTemplate()
				toolBar.Parent = window.GuiElems.Content
				treeFrame.Parent = window.GuiElems.Content
				explorerItems.ScrollCorner.Parent = window.GuiElems.Content
				scrollV.Gui.Parent = window.GuiElems.Content
				scrollH.Gui.Parent = window.GuiElems.Content

				-- Init stuff that requires the window
				Explorer.InitRenameBox()
				Explorer.InitSearch()
				Explorer.InitDelCleaner()
				selection.Changed:Connect(Explorer.UpdateSelectionVisuals)

				-- Window events
				window.GuiElems.Main:GetPropertyChangedSignal("AbsoluteSize"):Connect(function()
					if Explorer.Active then
						Explorer.UpdateView()
						Explorer.Refresh()
					end
				end)
				window.OnActivate:Connect(function()
					Explorer.Active = true
					Explorer.UpdateView()
					Explorer.Update()
					Explorer.Refresh()
				end)
				window.OnRestore:Connect(function()
					Explorer.Active = true
					Explorer.UpdateView()
					Explorer.Update()
					Explorer.Refresh()
				end)
				window.OnDeactivate:Connect(function() Explorer.Active = false end)
				window.OnMinimize:Connect(function() Explorer.Active = false end)

				-- Settings
				autoUpdateSearch = Settings.Explorer.AutoUpdateSearch

				-- Fill in nodes
				nodes[game] = {Obj = game}
				expanded[nodes[game]] = true

				-- Nil Instances
				if env.getnilinstances then
					nodes[nilNode.Obj] = nilNode
				end

				Explorer.SetupConnections()

				local insts = getDescendants(game)
				if Main.Elevated then
					for i = 1,#insts do
						local obj = insts[i]
						local par = nodes[ffa(obj,"Instance")]
						if not par then continue end
						local newNode = {
							Obj = obj,
							Parent = par,
						}
						nodes[obj] = newNode
						par[#par+1] = newNode
					end
				else
					for i = 1,#insts do
						local obj = insts[i]
						local s,parObj = pcall(ffa,obj,"Instance")
						local par = nodes[parObj]
						if not par then continue end
						local newNode = {
							Obj = obj,
							Parent = par,
						}
						nodes[obj] = newNode
						par[#par+1] = newNode
					end
				end
			end

			return Explorer
		end

		return {InitDeps = initDeps, InitAfterMain = initAfterMain, Main = main}
	end,
	Properties = function()
--[[
	Properties App Module
	
	The main properties interface
]]

		-- Common Locals
		local Main,Lib,Apps,Settings -- Main Containers
		local Explorer, Properties, ScriptViewer, Notebook -- Major Apps
		local API,RMD,env,service,plr,create,createSimple -- Main Locals

		local function initDeps(data)
			Main = data.Main
			Lib = data.Lib
			Apps = data.Apps
			Settings = data.Settings

			API = data.API
			RMD = data.RMD
			env = data.env
			service = data.service
			plr = data.plr
			create = data.create
			createSimple = data.createSimple
		end

		local function initAfterMain()
			Explorer = Apps.Explorer
			Properties = Apps.Properties
			ScriptViewer = Apps.ScriptViewer
			Notebook = Apps.Notebook
		end

		local function main()
			local Properties = {}

			local window, toolBar, propsFrame
			local scrollV, scrollH
			local categoryOrder
			local props,viewList,expanded,indexableProps,propEntries,autoUpdateObjs = {},{},{},{},{},{}
			local inputBox,inputTextBox,inputProp
			local checkboxes,propCons = {},{}
			local table,string = table,string
			local getPropChangedSignal = game.GetPropertyChangedSignal
			local getAttributeChangedSignal = game.GetAttributeChangedSignal
			local isa = game.IsA
			local getAttribute = game.GetAttribute
			local setAttribute = game.SetAttribute

			Properties.GuiElems = {}
			Properties.Index = 0
			Properties.ViewWidth = 0
			Properties.MinInputWidth = 100
			Properties.EntryIndent = 16
			Properties.EntryOffset = 4
			Properties.NameWidthCache = {}
			Properties.SubPropCache = {}
			Properties.ClassLists = {}
			Properties.SearchText = ""

			Properties.AddAttributeProp = {Category = "属性", Class = "", Name = "", SpecialRow = "AddAttribute", Tags = {}}
			Properties.SoundPreviewProp = {Category = "Data", ValueType = {Name = "SoundPlayer"}, Class = "Sound", Name = "Preview", Tags = {}}

			Properties.IgnoreProps = {
				["DataModel"] = {
					["PrivateServerId"] = true,
					["PrivateServerOwnerId"] = true,
					["VIPServerId"] = true,
					["VIPServerOwnerId"] = true
				}
			}

			Properties.ExpandableTypes = {
				["Vector2"] = true,
				["Vector3"] = true,
				["UDim"] = true,
				["UDim2"] = true,
				["CFrame"] = true,
				["Rect"] = true,
				["PhysicalProperties"] = true,
				["Ray"] = true,
				["NumberRange"] = true,
				["Faces"] = true,
				["Axes"] = true
			}

			Properties.ExpandableProps = {
				["Sound.SoundId"] = true
			}

			Properties.CollapsedCategories = {
				["Surface Inputs"] = true,
				["Surface"] = true
			}

			Properties.ConflictSubProps = {
				["Vector2"] = {"X","Y"},
				["Vector3"] = {"X","Y","Z"},
				["UDim"] = {"Scale","Offset"},
				["UDim2"] = {"X","X.Scale","X.Offset","Y","Y.Scale","Y.Offset"},
				["CFrame"] = {"Position","Position.X","Position.Y","Position.Z",
					"RightVector","RightVector.X","RightVector.Y","RightVector.Z",
					"UpVector","UpVector.X","UpVector.Y","UpVector.Z",
					"LookVector","LookVector.X","LookVector.Y","LookVector.Z"},
				["Rect"] = {"Min.X","Min.Y","Max.X","Max.Y"},
				["PhysicalProperties"] = {"Density","Elasticity","ElasticityWeight","Friction","FrictionWeight"},
				["Ray"] = {"Origin","Origin.X","Origin.Y","Origin.Z","Direction","Direction.X","Direction.Y","Direction.Z"},
				["NumberRange"] = {"Min","Max"},
				["Faces"] = {"Back","Bottom","Front","Left","Right","Top"},
				["Axes"] = {"X","Y","Z"}
			}

			Properties.ConflictIgnore = {
				["BasePart"] = {
					["ResizableFaces"] = true
				}
			}

			Properties.RoundableTypes = {
				["float"] = true,
				["double"] = true,
				["Color3"] = true,
				["UDim"] = true,
				["UDim2"] = true,
				["Vector2"] = true,
				["Vector3"] = true,
				["NumberRange"] = true,
				["Rect"] = true,
				["NumberSequence"] = true,
				["ColorSequence"] = true,
				["Ray"] = true,
				["CFrame"] = true
			}

			Properties.TypeNameConvert = {
				["number"] = "double",
				["boolean"] = "bool"
			}

			Properties.ToNumberTypes = {
				["int"] = true,
				["int64"] = true,
				["float"] = true,
				["double"] = true
			}

			Properties.DefaultPropValue = {
				string = "",
				bool = false,
				double = 0,
				UDim = UDim.new(0,0),
				UDim2 = UDim2.new(0,0,0,0),
				BrickColor = BrickColor.new("Medium stone grey"),
				Color3 = Color3.new(1,1,1),
				Vector2 = Vector2.new(0,0),
				Vector3 = Vector3.new(0,0,0),
				NumberSequence = NumberSequence.new(1),
				ColorSequence = ColorSequence.new(Color3.new(1,1,1)),
				NumberRange = NumberRange.new(0),
				Rect = Rect.new(0,0,0,0)
			}

			Properties.AllowedAttributeTypes = {"string","boolean","number","UDim","UDim2","BrickColor","Color3","Vector2","Vector3","NumberSequence","ColorSequence","NumberRange","Rect"}

			Properties.StringToValue = function(prop,str)
				local typeData = prop.ValueType
				local typeName = typeData.Name

				if typeName == "string" or typeName == "Content" then
					return str
				elseif Properties.ToNumberTypes[typeName] then
					return tonumber(str)
				elseif typeName == "Vector2" then
					local vals = str:split(",")
					local x,y = tonumber(vals[1]),tonumber(vals[2])
					if x and y and #vals >= 2 then return Vector2.new(x,y) end
				elseif typeName == "Vector3" then
					local vals = str:split(",")
					local x,y,z = tonumber(vals[1]),tonumber(vals[2]),tonumber(vals[3])
					if x and y and z and #vals >= 3 then return Vector3.new(x,y,z) end
				elseif typeName == "UDim" then
					local vals = str:split(",")
					local scale,offset = tonumber(vals[1]),tonumber(vals[2])
					if scale and offset and #vals >= 2 then return UDim.new(scale,offset) end
				elseif typeName == "UDim2" then
					local vals = str:gsub("[{}]",""):split(",")
					local xScale,xOffset,yScale,yOffset = tonumber(vals[1]),tonumber(vals[2]),tonumber(vals[3]),tonumber(vals[4])
					if xScale and xOffset and yScale and yOffset and #vals >= 4 then return UDim2.new(xScale,xOffset,yScale,yOffset) end
				elseif typeName == "CFrame" then
					local vals = str:split(",")
					local s,result = pcall(CFrame.new, unpack(vals))
					if s and #vals >= 12 then return result end
				elseif typeName == "Rect" then
					local vals = str:split(",")
					local s,result = pcall(Rect.new,unpack(vals))
					if s and #vals >= 4 then return result end
				elseif typeName == "Ray" then
					local vals = str:gsub("[{}]",""):split(",")
					local s,origin = pcall(Vector3.new,unpack(vals,1,3))
					local s2,direction = pcall(Vector3.new,unpack(vals,4,6))
					if s and s2 and #vals >= 6 then return Ray.new(origin,direction) end
				elseif typeName == "NumberRange" then
					local vals = str:split(",")
					local s,result = pcall(NumberRange.new,unpack(vals))
					if s and #vals >= 1 then return result end
				elseif typeName == "Color3" then
					local vals = str:gsub("[{}]",""):split(",")
					local s,result = pcall(Color3.fromRGB,unpack(vals))
					if s and #vals >= 3 then return result end
				end

				return nil
			end

			Properties.ValueToString = function(prop,val)
				local typeData = prop.ValueType
				local typeName = typeData.Name

				if typeName == "Color3" then
					return Lib.ColorToBytes(val)
				elseif typeName == "NumberRange" then
					return val.Min..", "..val.Max
				end

				return tostring(val)
			end

			Properties.GetIndexableProps = function(obj,classData)
				if not Main.Elevated then
					if not pcall(function() return obj.ClassName end) then return nil end
				end

				local ignoreProps = Properties.IgnoreProps[classData.Name] or {}

				local result = {}
				local count = 1
				local props = classData.Properties
				for i = 1,#props do
					local prop = props[i]
					if not ignoreProps[prop.Name] then
						local s = pcall(function() return obj[prop.Name] end)
						if s then
							result[count] = prop
							count = count + 1
						end
					end
				end

				return result
			end

			Properties.FindFirstObjWhichIsA = function(class)
				local classList = Properties.ClassLists[class] or {}
				if classList and #classList > 0 then
					return classList[1]
				end

				return nil
			end

			Properties.ComputeConflicts = function(p)
				local maxConflictCheck = Settings.Properties.MaxConflictCheck
				local sList = Explorer.Selection.List
				local classLists = Properties.ClassLists
				local stringSplit = string.split
				local t_clear = table.clear
				local conflictIgnore = Properties.ConflictIgnore
				local conflictMap = {}
				local propList = p and {p} or props

				if p then
					local gName = p.Class.."."..p.Name
					autoUpdateObjs[gName] = nil
					local subProps = Properties.ConflictSubProps[p.ValueType.Name] or {}
					for i = 1,#subProps do
						autoUpdateObjs[gName.."."..subProps[i]] = nil
					end
				else
					table.clear(autoUpdateObjs)
				end

				if #sList > 0 then
					for i = 1,#propList do
						local prop = propList[i]
						local propName,propClass = prop.Name,prop.Class
						local typeData = prop.RootType or prop.ValueType
						local typeName = typeData.Name
						local attributeName = prop.AttributeName
						local gName = propClass.."."..propName

						local checked = 0
						local subProps = Properties.ConflictSubProps[typeName] or {}
						local subPropCount = #subProps
						local toCheck = subPropCount + 1
						local conflictsFound = 0
						local indexNames = {}
						local ignored = conflictIgnore[propClass] and conflictIgnore[propClass][propName]
						local truthyCheck = (typeName == "PhysicalProperties")
						local isAttribute = prop.IsAttribute
						local isMultiType = prop.MultiType

						t_clear(conflictMap)

						if not isMultiType then
							local firstVal,firstObj,firstSet
							local classList = classLists[prop.Class] or {}
							for c = 1,#classList do
								local obj = classList[c]
								if not firstSet then
									if isAttribute then
										firstVal = getAttribute(obj,attributeName)
										if firstVal ~= nil then
											firstObj = obj
											firstSet = true
										end
									else
										firstVal = obj[propName]
										firstObj = obj
										firstSet = true
									end
									if ignored then break end
								else
									local propVal,skip
									if isAttribute then
										propVal = getAttribute(obj,attributeName)
										if propVal == nil then skip = true end
									else
										propVal = obj[propName]
									end

									if not skip then
										if not conflictMap[1] then
											if truthyCheck then
												if (firstVal and true or false) ~= (propVal and true or false) then
													conflictMap[1] = true
													conflictsFound = conflictsFound + 1
												end
											elseif firstVal ~= propVal then
												conflictMap[1] = true
												conflictsFound = conflictsFound + 1
											end
										end

										if subPropCount > 0 then
											for sPropInd = 1,subPropCount do
												local indexes = indexNames[sPropInd]
												if not indexes then indexes = stringSplit(subProps[sPropInd],".") indexNames[sPropInd] = indexes end

												local firstValSub = firstVal
												local propValSub = propVal

												for j = 1,#indexes do
													if not firstValSub or not propValSub then break end -- PhysicalProperties
													local indexName = indexes[j]
													firstValSub = firstValSub[indexName]
													propValSub = propValSub[indexName]
												end

												local mapInd = sPropInd + 1
												if not conflictMap[mapInd] and firstValSub ~= propValSub then
													conflictMap[mapInd] = true
													conflictsFound = conflictsFound + 1
												end
											end
										end

										if conflictsFound == toCheck then break end
									end
								end

								checked = checked + 1
								if checked == maxConflictCheck then break end
							end

							if not conflictMap[1] then autoUpdateObjs[gName] = firstObj end
							for sPropInd = 1,subPropCount do
								if not conflictMap[sPropInd+1] then
									autoUpdateObjs[gName.."."..subProps[sPropInd]] = firstObj
								end
							end
						end
					end
				end

				if p then
					Properties.Refresh()
				end
			end

			-- Fetches the properties to be displayed based on the explorer selection
			Settings.Properties.ShowAttributes = true -- im making it true anyway since its useful by default and people complain
			Properties.ShowExplorerProps = function()
				local maxConflictCheck = Settings.Properties.MaxConflictCheck
				local sList = Explorer.Selection.List
				local foundClasses = {}
				local propCount = 1
				local elevated = Main.Elevated
				local showDeprecated,showHidden = Settings.Properties.ShowDeprecated,Settings.Properties.ShowHidden
				local Classes = API.Classes
				local classLists = {}
				local lower = string.lower
				local RMDCustomOrders = RMD.PropertyOrders
				local getAttributes = game.GetAttributes
				local maxAttrs = Settings.Properties.MaxAttributes
				local showingAttrs = Settings.Properties.ShowAttributes
				local foundAttrs = {}
				local attrCount = 0
				local typeof = typeof
				local typeNameConvert = Properties.TypeNameConvert

				table.clear(props)

				for i = 1,#sList do
					local node = sList[i]
					local obj = node.Obj
					local class = node.Class
					if not class then class = obj.ClassName node.Class = class end

					local apiClass = Classes[class]
					while apiClass do
						local APIClassName = apiClass.Name
						if not foundClasses[APIClassName] then
							local apiProps = indexableProps[APIClassName]
							if not apiProps then apiProps = Properties.GetIndexableProps(obj,apiClass) indexableProps[APIClassName] = apiProps end

							for i = 1,#apiProps do
								local prop = apiProps[i]
								local tags = prop.Tags
								if (not tags.Deprecated or showDeprecated) and (not tags.Hidden or showHidden) then
									props[propCount] = prop
									propCount = propCount + 1
								end
							end
							foundClasses[APIClassName] = true
						end

						local classList = classLists[APIClassName]
						if not classList then classList = {} classLists[APIClassName] = classList end
						classList[#classList+1] = obj

						apiClass = apiClass.Superclass
					end

					if showingAttrs and attrCount < maxAttrs then
						local attrs = getAttributes(obj)
						for name,val in pairs(attrs) do
							local typ = typeof(val)
							if not foundAttrs[name] then
								local category = (typ == "Instance" and "Class") or (typ == "EnumItem" and "Enum") or "Other"
								local valType = {Name = typeNameConvert[typ] or typ, Category = category}
								local attrProp = {IsAttribute = true, Name = "ATTR_"..name, AttributeName = name, DisplayName = name, Class = "Instance", ValueType = valType, Category = "Attributes", Tags = {}}
								props[propCount] = attrProp
								propCount = propCount + 1
								attrCount = attrCount + 1
								foundAttrs[name] = {typ,attrProp}
								if attrCount == maxAttrs then break end
							elseif foundAttrs[name][1] ~= typ then
								foundAttrs[name][2].MultiType = true
								foundAttrs[name][2].Tags.ReadOnly = true
								foundAttrs[name][2].ValueType = {Name = "string"}
							end
						end
					end
				end

				table.sort(props,function(a,b)
					if a.Category ~= b.Category then
						return (categoryOrder[a.Category] or 9999) < (categoryOrder[b.Category] or 9999)
					else
						local aOrder = (RMDCustomOrders[a.Class] and RMDCustomOrders[a.Class][a.Name]) or 9999999
						local bOrder = (RMDCustomOrders[b.Class] and RMDCustomOrders[b.Class][b.Name]) or 9999999
						if aOrder ~= bOrder then
							return aOrder < bOrder
						else
							return lower(a.Name) < lower(b.Name)
						end
					end
				end)

				-- Find conflicts and get auto-update instances
				Properties.ClassLists = classLists
				Properties.ComputeConflicts()
				--warn("CONFLICT",tick()-start)
				if #props > 0 then
					props[#props+1] = Properties.AddAttributeProp
				end

				Properties.Update()
				Properties.Refresh()
			end

			Properties.UpdateView = function()
				local maxEntries = math.ceil(propsFrame.AbsoluteSize.Y / 23)
				local maxX = propsFrame.AbsoluteSize.X
				local totalWidth = Properties.ViewWidth + Properties.MinInputWidth

				scrollV.VisibleSpace = maxEntries
				scrollV.TotalSpace = #viewList + 1
				scrollH.VisibleSpace = maxX
				scrollH.TotalSpace = totalWidth

				scrollV.Gui.Visible = #viewList + 1 > maxEntries
				scrollH.Gui.Visible = Settings.Properties.ScaleType == 0 and totalWidth > maxX

				local oldSize = propsFrame.Size
				propsFrame.Size = UDim2.new(1,(scrollV.Gui.Visible and -16 or 0),1,(scrollH.Gui.Visible and -39 or -23))
				if oldSize ~= propsFrame.Size then
					Properties.UpdateView()
				else
					scrollV:Update()
					scrollH:Update()

					if scrollV.Gui.Visible and scrollH.Gui.Visible then
						scrollV.Gui.Size = UDim2.new(0,16,1,-39)
						scrollH.Gui.Size = UDim2.new(1,-16,0,16)
						Properties.Window.GuiElems.Content.ScrollCorner.Visible = true
					else
						scrollV.Gui.Size = UDim2.new(0,16,1,-23)
						scrollH.Gui.Size = UDim2.new(1,0,0,16)
						Properties.Window.GuiElems.Content.ScrollCorner.Visible = false
					end

					Properties.Index = scrollV.Index
				end
			end

			Properties.MakeSubProp = function(prop,subName,valueType,displayName)
				local subProp = {}
				for i,v in pairs(prop) do
					subProp[i] = v
				end
				subProp.RootType = subProp.RootType or subProp.ValueType
				subProp.ValueType = valueType
				subProp.SubName = subProp.SubName and (subProp.SubName..subName) or subName
				subProp.DisplayName = displayName

				return subProp
			end

			Properties.GetExpandedProps = function(prop) -- TODO: Optimize using table
				local result = {}
				local typeData = prop.ValueType
				local typeName = typeData.Name
				local makeSubProp = Properties.MakeSubProp

				if typeName == "Vector2" then
					result[1] = makeSubProp(prop,".X",{Name = "float"})
					result[2] = makeSubProp(prop,".Y",{Name = "float"})
				elseif typeName == "Vector3" then
					result[1] = makeSubProp(prop,".X",{Name = "float"})
					result[2] = makeSubProp(prop,".Y",{Name = "float"})
					result[3] = makeSubProp(prop,".Z",{Name = "float"})
				elseif typeName == "CFrame" then
					result[1] = makeSubProp(prop,".Position",{Name = "Vector3"})
					result[2] = makeSubProp(prop,".RightVector",{Name = "Vector3"})
					result[3] = makeSubProp(prop,".UpVector",{Name = "Vector3"})
					result[4] = makeSubProp(prop,".LookVector",{Name = "Vector3"})
				elseif typeName == "UDim" then
					result[1] = makeSubProp(prop,".Scale",{Name = "float"})
					result[2] = makeSubProp(prop,".Offset",{Name = "int"})
				elseif typeName == "UDim2" then
					result[1] = makeSubProp(prop,".X",{Name = "UDim"})
					result[2] = makeSubProp(prop,".Y",{Name = "UDim"})
				elseif typeName == "Rect" then
					result[1] = makeSubProp(prop,".Min.X",{Name = "float"},"X0")
					result[2] = makeSubProp(prop,".Min.Y",{Name = "float"},"Y0")
					result[3] = makeSubProp(prop,".Max.X",{Name = "float"},"X1")
					result[4] = makeSubProp(prop,".Max.Y",{Name = "float"},"Y1")
				elseif typeName == "PhysicalProperties" then
					result[1] = makeSubProp(prop,".Density",{Name = "float"})
					result[2] = makeSubProp(prop,".Elasticity",{Name = "float"})
					result[3] = makeSubProp(prop,".ElasticityWeight",{Name = "float"})
					result[4] = makeSubProp(prop,".Friction",{Name = "float"})
					result[5] = makeSubProp(prop,".FrictionWeight",{Name = "float"})
				elseif typeName == "Ray" then
					result[1] = makeSubProp(prop,".Origin",{Name = "Vector3"})
					result[2] = makeSubProp(prop,".Direction",{Name = "Vector3"})
				elseif typeName == "NumberRange" then
					result[1] = makeSubProp(prop,".Min",{Name = "float"})
					result[2] = makeSubProp(prop,".Max",{Name = "float"})
				elseif typeName == "Faces" then
					result[1] = makeSubProp(prop,".Back",{Name = "bool"})
					result[2] = makeSubProp(prop,".Bottom",{Name = "bool"})
					result[3] = makeSubProp(prop,".Front",{Name = "bool"})
					result[4] = makeSubProp(prop,".Left",{Name = "bool"})
					result[5] = makeSubProp(prop,".Right",{Name = "bool"})
					result[6] = makeSubProp(prop,".Top",{Name = "bool"})
				elseif typeName == "Axes" then
					result[1] = makeSubProp(prop,".X",{Name = "bool"})
					result[2] = makeSubProp(prop,".Y",{Name = "bool"})
					result[3] = makeSubProp(prop,".Z",{Name = "bool"})
				end

				if prop.Name == "SoundId" and prop.Class == "Sound" then
					result[1] = Properties.SoundPreviewProp
				end

				return result
			end

			Properties.Update = function()
				table.clear(viewList)

				local nameWidthCache = Properties.NameWidthCache
				local lastCategory
				local count = 1
				local maxWidth,maxDepth = 0,1

				local textServ = service.TextService
				local getTextSize = textServ.GetTextSize
				local font = Enum.Font.SourceSans
				local size = Vector2.new(math.huge,20)
				local stringSplit = string.split
				local entryIndent = Properties.EntryIndent
				local isFirstScaleType = Settings.Properties.ScaleType == 0
				local find,lower = string.find,string.lower
				local searchText = (#Properties.SearchText > 0 and lower(Properties.SearchText))

				local function recur(props,depth)
					for i = 1,#props do
						local prop = props[i]
						local propName = prop.Name
						local subName = prop.SubName
						local category = prop.Category

						local visible
						if searchText and depth == 1 then
							if find(lower(propName),searchText,1,true) then
								visible = true
							end
						else
							visible = true
						end

						if visible and lastCategory ~= category then
							viewList[count] = {CategoryName = category}
							count = count + 1
							lastCategory = category
						end

						if (expanded["CAT_"..category] and visible) or prop.SpecialRow then
							if depth > 1 then prop.Depth = depth if depth > maxDepth then maxDepth = depth end end

							if isFirstScaleType then
								local nameArr = subName and stringSplit(subName,".")
								local displayName = prop.DisplayName or (nameArr and nameArr[#nameArr]) or propName

								local nameWidth = nameWidthCache[displayName]
								if not nameWidth then nameWidth = getTextSize(textServ,displayName,14,font,size).X nameWidthCache[displayName] = nameWidth end

								local totalWidth = nameWidth + entryIndent*depth
								if totalWidth > maxWidth then
									maxWidth = totalWidth
								end
							end

							viewList[count] = prop
							count = count + 1

							local fullName = prop.Class.."."..prop.Name..(prop.SubName or "")
							if expanded[fullName] then
								local nextDepth = depth+1
								local expandedProps = Properties.GetExpandedProps(prop)
								if #expandedProps > 0 then
									recur(expandedProps,nextDepth)
								end
							end
						end
					end
				end
				recur(props,1)

				inputProp = nil
				Properties.ViewWidth = maxWidth + 9 + Properties.EntryOffset
				Properties.UpdateView()
			end

			Properties.NewPropEntry = function(index)
				local newEntry = Properties.EntryTemplate:Clone()
				local nameFrame = newEntry.NameFrame
				local valueFrame = newEntry.ValueFrame
				local newCheckbox = Lib.Checkbox.new(1)
				newCheckbox.Gui.Position = UDim2.new(0,3,0,3)
				newCheckbox.Gui.Parent = valueFrame
				newCheckbox.OnInput:Connect(function()
					local prop = viewList[index + Properties.Index]
					if not prop then return end

					if prop.ValueType.Name == "PhysicalProperties" then
						Properties.SetProp(prop,newCheckbox.Toggled and true or nil)
					else
						Properties.SetProp(prop,newCheckbox.Toggled)
					end
				end)
				checkboxes[index] = newCheckbox

				local iconFrame = Main.MiscIcons:GetLabel()
				iconFrame.Position = UDim2.new(0,2,0,3)
				iconFrame.Parent = newEntry.ValueFrame.RightButton

				newEntry.Position = UDim2.new(0,0,0,23*(index-1))

				nameFrame.Expand.InputBegan:Connect(function(input)
					local prop = viewList[index + Properties.Index]
					if not prop or (input.UserInputType ~= Enum.UserInputType.MouseMovement and input.UserInputType ~= Enum.UserInputType.Touch) then return end

					local fullName = (prop.CategoryName and "CAT_"..prop.CategoryName) or prop.Class.."."..prop.Name..(prop.SubName or "")

					Main.MiscIcons:DisplayByKey(newEntry.NameFrame.Expand.Icon, expanded[fullName] and "Collapse_Over" or "Expand_Over")
				end)

				nameFrame.Expand.InputEnded:Connect(function(input)
					local prop = viewList[index + Properties.Index]
					if not prop or (input.UserInputType ~= Enum.UserInputType.MouseMovement and input.UserInputType ~= Enum.UserInputType.Touch) then return end

					local fullName = (prop.CategoryName and "CAT_"..prop.CategoryName) or prop.Class.."."..prop.Name..(prop.SubName or "")

					Main.MiscIcons:DisplayByKey(newEntry.NameFrame.Expand.Icon, expanded[fullName] and "Collapse" or "Expand")
				end)

				nameFrame.Expand.MouseButton1Down:Connect(function()
					local prop = viewList[index + Properties.Index]
					if not prop then return end

					local fullName = (prop.CategoryName and "CAT_"..prop.CategoryName) or prop.Class.."."..prop.Name..(prop.SubName or "")
					if not prop.CategoryName and not Properties.ExpandableTypes[prop.ValueType and prop.ValueType.Name] and not Properties.ExpandableProps[fullName] then return end

					expanded[fullName] = not expanded[fullName]
					Properties.Update()
					Properties.Refresh()
				end)

				nameFrame.PropName.InputBegan:Connect(function(input)
					local prop = viewList[index + Properties.Index]
					if not prop then return end
					if (input.UserInputType == Enum.UserInputType.MouseMovement or input.UserInputType == Enum.UserInputType.Touch) and not nameFrame.PropName.TextFits then
						local fullNameFrame = Properties.FullNameFrame	
						local nameArr = string.split(prop.Class.."."..prop.Name..(prop.SubName or ""), ".")
						local dispName = prop.DisplayName or nameArr[#nameArr]
						local sizeX = service.TextService:GetTextSize(dispName, 14, Enum.Font.SourceSans, Vector2.new(math.huge, 20)).X

						fullNameFrame.TextLabel.Text = dispName
						fullNameFrame.Size = UDim2.new(0, sizeX + 4, 0, 22)
						fullNameFrame.Visible = true
						Properties.FullNameFrameIndex = index
						Properties.FullNameFrameAttach.SetData(fullNameFrame, {Target = nameFrame})
						Properties.FullNameFrameAttach.Enable()
					end
				end)

				nameFrame.PropName.InputEnded:Connect(function(input)
					if (input.UserInputType == Enum.Us…"
 https://gitee.com/cmbhbh/cmbh/raw/master/Bex.lua#:~:text=%2D%2D%20https%3A//github.com,Start%0AMain.Init()
